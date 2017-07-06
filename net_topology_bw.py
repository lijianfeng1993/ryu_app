#coding:utf-8

import copy
import networkx as nx
from operator import attrgetter
from ryu.base import app_manager
from ryu.controller import ofp_event
from ryu.controller.handler import MAIN_DISPATCHER, DEAD_DISPATCHER
from ryu.controller.handler import CONFIG_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3
from ryu.lib import hub
from ryu.lib.packet import packet
from ryu.lib.packet import arp
from ryu.lib.packet import ethernet
from ryu.lib.packet import ipv4
from ryu.topology import event, switches
from ryu.topology.api import get_switch, get_link
import setting

class NetTopology(app_manager.RyuApp):
    """
        This App is to discover topology of networks
        and monitor the port stats
    """
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]


    def __init__(self, *args, **kwargs):
        super(NetTopology,self).__init__(self, *args, **kwargs)

        self.name = "NetTopology"
        self.topo = nx.DiGraph()
        self.link_dpid_pairs = []       # (src_dpid,dst_dpid)
        self.all_ports = {}          #   dpid -> (all_ports)
        self.link_ports = {}
        self.host_ports = {}
        self.link_dpid_to_port = {}  # (src_dpid,dst_dpid)->(src_port,dst_port)
        self.datapaths = {}
        self.hosts_link = {}        # (dpid,in_port)->(host_ip,host_mac)
        self.port_stats = {}       #(dpid,port)->(statistics) 
        self.port_bw_all = {}       #(dpid,port)->bw_all
        self.port_bw_in_use = {}    #(dpid,port)->bw_in_use
        self.port_bw_free = {}     #(dpid,port)->bw_free
        self.multipaths = {}
        self.best_paths = {}
        self.monitor_thread = hub.spawn(self.monitor)


    def get_link_dpid_paris_from_links(self):
        for link in self.links:
            src = link.src
            dst = link.dst
            self.link_dpid_pairs.append((src.dpid, dst.dpid))

    def get_all_ports(self):
        for sw in self.switches:
            dpid = sw.dp.id
            self.all_ports.setdefault(dpid, set())
            self.link_ports.setdefault(dpid, set())
            for port in sw.ports:
                self.all_ports[dpid].add(port.port_no)


    def get_link_dpid_to_port(self):
        for link in self.links:
            src = link.src
            dst = link.dst
            self.link_dpid_to_port[
                (src.dpid, dst.dpid)] = (src.port_no, dst.port_no)

            self.link_ports[src.dpid].add(src.port_no)
            if dst.dpid in self.all_ports.keys():
                self.link_ports[dst.dpid].add(dst.port_no)

    def get_host_ports(self):
        for dpid in self.all_ports:
            all_ports = self.all_ports[dpid]
            link_ports = self.link_ports[dpid]
            self.host_ports[dpid] = all_ports - link_ports

    def get_port_pairs_from_dpid_pairs(self, src_dpid, dst_dpid):
        for key in self.link_dpid_to_port.keys():
            if key == (src_dpid, dst_dpid):
                return self.link_dpid_to_port[key]

    def save_port_stats(self, dict, key, statistic):
        if key not in dict:
            dict[key] = []
        dict[key].append(statistic)

        if len(dict[key]) > 2:
            dict[key].pop(0)


    def calc_time(self, sec, nsec):
        return sec + nsec / (10 ** 9)

    def calc_interval(self, n_sec, n_nsec, p_sec, p_nsec):
        return self.calc_time(n_sec, n_nsec) - self.calc_time(p_sec, p_nsec)

    def calc_bw_in_use(self, start, end, interval):
        if interval:
            return (end - start) / (interval)
        else:
            return 0

    def calc_bw_free(self, bw_all, bw_in_use):
        # BW:Mbit/s
        return max(bw_all / 10**3 - bw_in_use * 8 / 10**6, 0)

    events = [event.EventSwitchEnter,
              event.EventSwitchLeave, event.EventPortAdd,
              event.EventPortDelete, event.EventPortModify,
              event.EventLinkAdd, event.EventLinkDelete]

    def get_host_sw_by_ip(self, ip):
        """
            Get host location info:(datapath, port) according to host ip.
        """
        for key in self.hosts_link.keys():
            if self.hosts_link[key][0] == ip:
                return key[0]
        self.logger.info("%s location is not found." % ip)
        return None

    def get_host_port_by_ip(self, ip):
        """
            Get host location info:(datapath, port) according to host ip.
        """
        for key in self.hosts_link.keys():
            if self.hosts_link[key][0] == ip:
                return key[1]
        self.logger.info("%s location is not found." % ip)
        return None


    def get_multi_path_from_topo(self, topo, weight='weight'):
        """
        Get all paths between switches in the topology
        """
        paths = {}
        topo_copy = copy.deepcopy(topo)
        for src in topo_copy.nodes():
            paths.setdefault(src, {})
            for dst in topo_copy.nodes():
                if src == dst:
                    paths[src][src] = [src]
                else:
                    paths[src].setdefault(dst, [])
                    generator = nx.shortest_simple_paths(topo, 
                                            source=src,target=dst, weight=weight)
                    for path in generator:
                        paths[src][dst].append(path)
        self.multipaths = paths


    def add_bw_to_topo(self, port_bw_free):
        for key in self.link_dpid_to_port:
            (src_dpid, dst_dpid) = key
            (src_port, dst_port) = self.link_dpid_to_port[key]
            if (src_dpid,src_port) in port_bw_free and (dst_dpid, dst_port) in port_bw_free:
                bw_src_port = port_bw_free[(src_dpid, src_port)]
                bw_dst_port = port_bw_free[(dst_dpid, dst_port)]
                bw = min(bw_src_port, bw_dst_port)
                self.topo[src_dpid][dst_dpid]['bw'] = bw
            else:
                self.topo[src_dpid][dst_dpid]['bw'] = 0

    def get_bw_of_path(self, path):
        """
            Get the bandwidth of a path.
        """
        length = len(path)
        if length > 1:
            min_bw = setting.MAX_CAPACITY
            for i in xrange(length - 1):
                pre, curr = path[i], path[i + 1]
                if 'bw' in self.topo[pre][curr]:
                    bw = self.topo[pre][curr]['bw']
                    min_bw = min(bw, min_bw)
                else:
                    continue
            return min_bw
        return setting.MAX_CAPACITY

    def get_best_path_by_bw(self):

        best_paths = copy.deepcopy(self.multipaths)

        for src in best_paths:
            for dst in best_paths[src]:
                if src == dst:
                    best_paths[src][src] = [src]
                else:
                    max_free_bw_of_paths = 0
                    best_path = best_paths[src][dst][0]
                    for path in best_paths[src][dst]:
                        bw_of_path = self.get_bw_of_path(path)
                        if bw_of_path > max_free_bw_of_paths:
                            max_free_bw_of_paths = bw_of_path
                            best_path = path

                    best_paths[src][dst] = best_path
        self.best_paths = best_paths

    def add_flow(self, dp, p, match, actions, idle_timeout=0, hard_timeout=0):
        """
            Send a flow entry to datapath.
        """
        ofproto = dp.ofproto
        parser = dp.ofproto_parser

        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
                                             actions)]

        mod = parser.OFPFlowMod(datapath=dp, priority=p,
                                idle_timeout=idle_timeout,
                                hard_timeout=hard_timeout,
                                match=match, instructions=inst)
        dp.send_msg(mod)

    def send_flow_mod(self, datapath, flow_info, src_port, dst_port):
        """
            send flow entry to datapath.
        """
        parser = datapath.ofproto_parser
        actions = []

        match = parser.OFPMatch(
            in_port=src_port, eth_type=flow_info[0],
            ipv4_src=flow_info[1], ipv4_dst=flow_info[2])

        actions.append(parser.OFPActionOutput(dst_port))

        self.add_flow(datapath, 1, match, actions,
                      idle_timeout=5, hard_timeout=70)

    def _build_packet_out(self, datapath, buffer_id, src_port, dst_port, data):
        """
            Build packet out object.
        """
        actions = []
        if dst_port:
            actions.append(datapath.ofproto_parser.OFPActionOutput(dst_port))

        msg_data = None
        if buffer_id == datapath.ofproto.OFP_NO_BUFFER:
            if data is None:
                return None
            msg_data = data

        out = datapath.ofproto_parser.OFPPacketOut(
            datapath=datapath, buffer_id=buffer_id,
            data=msg_data, in_port=src_port, actions=actions)
        return out


    def send_packet_out(self, datapath, buffer_id, src_port, dst_port, data):
        """
            Send packet out packet to assigned datapath.
        """
        out = self._build_packet_out(datapath, buffer_id,
                                     src_port, dst_port, data)
        if out:
            datapath.send_msg(out)

    def install_flow_for_first_dp(self, path, flow_info, buffer_id, data, back_info):

        in_port = flow_info[3]
        first_dp = self.datapaths[path[0]]
        ports = self.get_port_pairs_from_dpid_pairs(path[0], path[1])
        out_port = ports[0]
        self.send_flow_mod(first_dp, flow_info, in_port, out_port)
        self.send_flow_mod(first_dp, back_info, out_port, in_port)
        self.send_packet_out(first_dp, buffer_id, in_port, out_port, data)

    def install_flow_for_last_dp(self, path, flow_info, back_info):

        ports = self.get_port_pairs_from_dpid_pairs(path[-2], path[-1])
        in_port = ports[1]
        out_port = self.get_host_port_by_ip(flow_info[2])
        last_dp = self.datapaths[path[-1]]
        self.send_flow_mod(last_dp, flow_info, in_port, out_port)
        self.send_flow_mod(last_dp, back_info, out_port, in_port)

    def install_flow_for_middle_dp(self, path, flow_info, back_info):

        for i in xrange(1, len(path)-1):
            port = self.get_port_pairs_from_dpid_pairs(path[i-1], path[i])
            port_next = self.get_port_pairs_from_dpid_pairs(path[i], path[i+1])
            if port and port_next:
                in_port, out_port = port[1], port_next[0]
                datapath = self.datapaths[path[i]]
                self.send_flow_mod(datapath, flow_info, in_port, out_port)
                self.send_flow_mod(datapath, back_info, out_port, in_port)

    def install_flow(self, path, flow_info, buffer_id, data=None):

        in_port = flow_info[3]
        first_dp = self.datapaths[path[0]]
        back_info = (flow_info[0], flow_info[2], flow_info[1])
        if len(path) > 2:
            self.install_flow_for_middle_dp(path, flow_info, back_info)
        if len(path) > 1:
            self.install_flow_for_first_dp(path, flow_info, buffer_id, data, back_info)
            self.install_flow_for_last_dp(path, flow_info, back_info)
        else:
            out_port = self.get_host_port_by_ip(flow_info[2])
            self.send_flow_mod(first_dp, flow_info, in_port, out_port)
            self.send_flow_mod(first_dp, back_info, out_port, in_port)
            self.send_packet_out(first_dp, buffer_id, in_port, out_port, data)

    def ip_forwarding(self, msg, eth_type, ip_src, ip_dst):
        dp = msg.datapath
        in_port = msg.match['in_port']
        src_dpid = dp.id
        dst_dpid = self.get_host_sw_by_ip(ip_dst)
        if dst_dpid:

            path = self.best_paths.get(src_dpid).get(dst_dpid)
            self.logger.info("[PATH]%s<-->%s: %s" % (ip_src, ip_dst, path))
            flow_info = (eth_type, ip_src, ip_dst, in_port)
            # install flow entries to datapath along side the path.
            self.install_flow(path, flow_info, msg.buffer_id, msg.data)


    def flood(self, msg):
        """
            Flood ARP packet to the access port
            which has no record of host.
        """
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        for dpid in self.host_ports:
            for port in self.host_ports[dpid]:
                if (dpid, port) not in self.hosts_link.keys():
                    datapath = self.datapaths[dpid]
                    out = self._build_packet_out(
                        datapath, ofproto.OFP_NO_BUFFER,
                        ofproto.OFPP_CONTROLLER, port, msg.data)
                    datapath.send_msg(out)
        self.logger.debug("Flooding msg")

    def arp_forwarding(self, msg, src_ip, dst_ip):
        """ Send ARP packet to the destination host,
            if the dst host record is existed,
            else, flow it to the unknow access port.
        """
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        datapath_dst = self.get_host_sw_by_ip(dst_ip)
        out_port = self.get_host_port_by_ip(dst_ip)
        if datapath_dst:  # host record in access table.
            datapath = self.datapaths[datapath_dst]
            out = self._build_packet_out(datapath, ofproto.OFP_NO_BUFFER,
                                         ofproto.OFPP_CONTROLLER,
                                         out_port, msg.data)
            datapath.send_msg(out)
            self.logger.debug("Reply ARP to knew host")
        else:
            self.flood(msg)



    @set_ev_cls(events)
    def create_topo(self, ev):
        self.switches = get_switch(self, None)
        self.links = get_link(self, None)
        self.get_all_ports()
        self.get_link_dpid_paris_from_links()
        self.get_link_dpid_to_port()
        self.get_host_ports()
        for src in self.datapaths.values():
            for dst in self.datapaths.values():
                if src.id == dst.id:
                    self.topo.add_edge(src.id, dst.id, weight=0)
                elif (src.id, dst.id) in self.link_dpid_pairs:
                    self.topo.add_edge(src.id, dst.id, weight=1)



    def send_requests(self):
        for dp in self.datapaths.values():
            ofproto = dp.ofproto
            parser = dp.ofproto_parser
            request = parser.OFPPortDescStatsRequest(dp, 0)
            dp.send_msg(request)

            request = parser.OFPPortStatsRequest(dp, 0, ofproto.OFPP_ANY)
            dp.send_msg(request)

            request = parser.OFPFlowStatsRequest(dp)
            dp.send_msg(request)


    def monitor(self):
        while True:
            self.create_topo(None)
            self.get_multi_path_from_topo(self.topo, weight='weight')
            self.send_requests()
            self.add_bw_to_topo(self.port_bw_free)
            self.get_best_path_by_bw()
            hub.sleep(8)
            self.show_topo()
            hub.sleep(1)


    @set_ev_cls(ofp_event.EventOFPStateChange,
                [MAIN_DISPATCHER, DEAD_DISPATCHER])
    def _state_change_handler(self, ev):
        """
            Record datapath's info
        """
        datapath = ev.datapath
        if ev.state == MAIN_DISPATCHER:
            if not datapath.id in self.datapaths:
                self.logger.debug('register datapath: %016x', datapath.id)
                self.datapaths[datapath.id] = datapath
        elif ev.state == DEAD_DISPATCHER:
            if datapath.id in self.datapaths:
                self.logger.debug('unregister datapath: %016x', datapath.id)
                del self.datapaths[datapath.id]

    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def get_hosts_link(self, ev):

        # Get the hosts by arp packets

        msg = ev.msg
        datapath = msg.datapath
        dpid = datapath.id
        in_port = msg.match['in_port']
        pkt = packet.Packet(msg.data)

        arp_pkt = pkt.get_protocol(arp.arp)
        if arp_pkt:
            ip = arp_pkt.src_ip   
            mac = arp_pkt.src_mac
            if (dpid, in_port) in self.hosts_link:
                return
            else:
                self.hosts_link.setdefault((dpid, in_port), None)
                self.hosts_link[(dpid, in_port)] = (ip, mac)


    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def forward(self, ev):
        '''
            forward the packets according to the PacketIn message
        '''
        msg = ev.msg
        datapath = msg.datapath
        pkt = packet.Packet(msg.data)
        arp_pkt = pkt.get_protocol(arp.arp)
        ip_pkt = pkt.get_protocol(ipv4.ipv4)

        if isinstance(arp_pkt, arp.arp):
            self.arp_forwarding(msg, arp_pkt.src_ip, arp_pkt.dst_ip)

        if isinstance(ip_pkt, ipv4.ipv4):
            if len(pkt.get_protocols(ethernet.ethernet)):
                eth_type = pkt.get_protocols(ethernet.ethernet)[0].ethertype
                self.ip_forwarding(msg, eth_type, ip_pkt.src, ip_pkt.dst)


    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def port_stats_reply(self ,ev):
        """
        save and handle the port statistics to 
        calcuate the usage of bandwidth of each port

        """
        msg = ev.msg
        dp = msg.datapath
        dpid = dp.id
        body = msg.body

        for stat in sorted(body, key=attrgetter('port_no')):
            port_no = stat.port_no
            if port_no != ofproto_v1_3.OFPP_LOCAL:
                statistic = (stat.rx_bytes, stat.tx_bytes, stat.rx_errors,
                         stat.duration_sec, stat.duration_nsec)
                key = (dpid, port_no)
                self.save_port_stats(self.port_stats, key, statistic)

                start_all_bytes = 0
                interval = 10
                statistic = self.port_stats[key]
                if len(statistic) > 1:
                    start_all_bytes = statistic[-2][0] + statistic[-2][1]
                    interval = self.calc_interval(statistic[-1][3], statistic[-1][4],
                                              statistic[-2][3], statistic[-2][4])

                end_all_bytes = statistic[-1][0] + statistic[-1][1]

                bw_in_use = self.calc_bw_in_use(start_all_bytes, end_all_bytes, interval)
                self.port_bw_in_use[key] = bw_in_use

                bw_free = self.calc_bw_free(self.port_bw_all[key], bw_in_use)
                self.port_bw_free[key] = bw_free



    @set_ev_cls(ofp_event.EventOFPPortDescStatsReply, MAIN_DISPATCHER)
    def port_desc_stats_reply(self, ev):
        msg = ev.msg
        body = msg.body
        dp = msg.datapath
        dpid = dp.id

        for stat in body:
            port_no = stat.port_no
            key = (dpid, port_no)
            self.port_bw_all[key] = stat.curr_speed


    def show_topo(self):
        print "———————————————————Network Topology(port,port)————————————————"
        print '%s' % ("switch"),
        for i in self.topo.nodes():
            print '%12d' % i,
        print ""
        for i in self.topo.nodes():
            print '%3d   ' % i,
            for j in self.topo.nodes():
                if (i, j) in self.link_dpid_to_port.keys():
                    print '%12s' % str(self.link_dpid_to_port[(i, j)]),
                else:
                    print '%12s' % "No Link",
            print ""
        print ""

        print "———————————————————————————Hosts(ip,mac)————————————————————————"
        print '%s' % ("(switch,port)"), '%25s' % ("Hosts")
        for key in self.hosts_link:
            print '  ', key, '       ', self.hosts_link[key]
        print ""

        print "——————————————————————————————Port Statistics———————————————————————————"

        print('      dpid             port     rx_bytes     tx_bytes     rx_errors'
            '        bw_in_use        bw_free')
        format = '%016x %8x %12d %12d %12d %16d %16d'
        for dpid in self.datapaths.keys():
            for key in self.port_stats.keys():
                if key[0] == dpid:
                    statistic = self.port_stats[key]
                    bw_in_use = self.port_bw_in_use[key]
                    bw_free = self.port_bw_free[key]
                    print(format % (key[0], key[1], statistic[-1][0], statistic[-1][1],
                        statistic[-1][2], bw_in_use, bw_free))
        print ""

