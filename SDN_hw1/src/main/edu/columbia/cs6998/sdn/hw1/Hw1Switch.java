/**
*    Copyright 2014, Columbia University.
*    Homework 1, COMS E6998-10 Fall 2014
*    Software Defined Networking
*    Originally created by Shangjin Zhang, Columbia University
*
*    Licensed under the Apache License, Version 2.0 (the "License"); you may
*    not use this file except in compliance with the License. You may obtain
*    a copy of the License at
*
*         http://www.apache.org/licenses/LICENSE-2.0
*
*    Unless required by applicable law or agreed to in writing, software
*    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
*    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
*    License for the specific language governing permissions and limitations
*    under the License.
**/

/**
 * Floodlight
 * A BSD licensed, Java based OpenFlow controller
 *
 * Floodlight is a Java based OpenFlow controller originally written by David Erickson at Stanford
 * University. It is available under the BSD license.
 *
 * For documentation, forums, issue tracking and more visit:
 *
 * http://www.openflowhub.org/display/Floodlight/Floodlight+Home
 **/

package edu.columbia.cs6998.sdn.hw1;

import java.util.Iterator;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Vector;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentHashMap;

import java.io.IOException;
import java.nio.ByteBuffer;

import net.floodlightcontroller.core.FloodlightContext;
import net.floodlightcontroller.core.IFloodlightProviderService;
import net.floodlightcontroller.core.IOFMessageListener;
import net.floodlightcontroller.core.IOFSwitch;
import net.floodlightcontroller.core.module.FloodlightModuleContext;
import net.floodlightcontroller.core.module.FloodlightModuleException;
import net.floodlightcontroller.core.module.IFloodlightModule;
import net.floodlightcontroller.core.module.IFloodlightService;

import net.floodlightcontroller.packet.Ethernet;
import net.floodlightcontroller.packet.IPv4;

import org.openflow.protocol.OFError;
import org.openflow.protocol.OFFlowMod;
import org.openflow.protocol.OFFlowRemoved;
import org.openflow.protocol.OFMatch;
import org.openflow.protocol.OFMessage;
import org.openflow.protocol.OFPacketIn;
import org.openflow.protocol.OFPacketOut;
import org.openflow.protocol.OFPort;
import org.openflow.protocol.OFType;

import org.openflow.protocol.action.OFAction;
import org.openflow.protocol.action.OFActionOutput;
import org.openflow.protocol.action.OFActionNetworkLayerAddress;
import org.openflow.protocol.action.OFActionDataLayer;
import org.openflow.protocol.action.OFActionDataLayerDestination;
import org.openflow.protocol.action.OFActionNetworkLayerDestination;
import org.openflow.protocol.action.OFActionDataLayerSource;
import org.openflow.protocol.action.OFActionNetworkLayerSource;

import org.openflow.util.HexString;
import org.openflow.util.LRULinkedHashMap;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class Hw1Switch implements IFloodlightModule, IOFMessageListener {

    protected static Logger log = LoggerFactory.getLogger(Hw1Switch.class);

    // Module dependencies
    protected IFloodlightProviderService floodlightProvider;

    // Stores the learned state for each switch: for each switch, we store <MAC addr, port>
    protected Map<IOFSwitch, Map<Long, Short>> macToSwitchPortMap;

    // Stores the number of links established <SourceAddr, <DestCnt, connectionCnt>>
    protected Map<Long, Map<Long, Long>> m_hostConnCnt;

    // Elephant flow counter Map<sw, Map<src, start_time>>
    protected Map<IOFSwitch, Map<Long, Long>> m_elephantFlowCnt;

    // @lfred: Web server addresses
    protected int m_webSvrIp;
    protected Map<Long, Integer> m_webSvr;  /* Mac, IP  */
    protected Map<Long, Long> m_svrStats;   /* Mac, Counter */

    // CS6998: data structures for the firewall feature
    // Stores the MAC address of hosts to block: <Macaddr, blockedTime>
    protected Map<Long, Long> blacklist;

    // flow-mod - for use in the cookie
    public static final int HW1_SWITCH_APP_ID = 10;
    // LOOK! This should probably go in some class that encapsulates
    // the app cookie management
    public static final int APP_ID_BITS = 12;
    public static final int APP_ID_SHIFT = (64 - APP_ID_BITS);
    public static final long HW1_SWITCH_COOKIE =
        (long) (HW1_SWITCH_APP_ID & ((1 << APP_ID_BITS) - 1)) << APP_ID_SHIFT;

    // more flow-mod defaults. We should not have idle timeout, but with hard timeout?
    protected static final short IDLE_TIMEOUT_DEFAULT   = 10;
    protected static final short HARD_TIMEOUT_DEFAULT   = 10;
    protected static final short PRIORITY_DEFAULT       = 100;
    protected static final short PRIORITY_HIGH          = 110;

    // for managing our map sizes
    protected static final int MAX_MACS_PER_SWITCH      = 1000;

    // maxinum allowed elephant flow number for one switch
    protected static final int MAX_ELEPHANT_FLOW_NUMBER = 2;

    // maximum allowed destination number for one host
    protected static final int MAX_DESTINATION_NUMBER   = 3;

    // maxinum allowed transmission rate: using 10 for test purpose
    protected static final int ELEPHANT_FLOW_BAND_WIDTH = 1000;

    // time duration the firewall will block each node for
    protected static final int FIREWALL_BLOCK_TIME_DUR  = (10 * 1000);

    // @lfred: load balance is ON
    protected boolean SvrLoadBalance = true;

    /**
     * @param floodlightProvider the floodlightProvider to set
     */
    public void setFloodlightProvider(IFloodlightProviderService aFloodlightProvider) {

        log.trace("[@lfred] setFloodlightProvider");
        this.floodlightProvider = aFloodlightProvider;
    }

    @Override
    public String getName() {
        return "hw1switch";
    }

    /* @lfred: update the blacklist entries according to the */
    protected void agingBlackList(long now) {

        java.util.Iterator<Map.Entry<Long, Long>> it = blacklist.entrySet().iterator();

        while (it.hasNext()) {
            Map.Entry<Long, Long> entry = it.next();

            if (now - entry.getValue().longValue() > FIREWALL_BLOCK_TIME_DUR)
                it.remove();
        }
    }

    /* check if a certain source is blocked */
    protected boolean isInBlackList(long sourceMac, long now) {

        Long blockTime = blacklist.get(Long.valueOf(sourceMac));

        if (blockTime != null) {
            if (now - blockTime.longValue() < FIREWALL_BLOCK_TIME_DUR) {
                log.info("[@lfred] host " + sourceMac + " is blocked. ");
                return true;
            }
        }

        return false;
    }

    protected void blockHost(long sourceMac, long now) {

        log.info("[@lfred] blocking " + sourceMac);

        blacklist.put(Long.valueOf(sourceMac), now);

        /* transformation long to byte[] */
        ByteBuffer buffer = ByteBuffer.allocate(Long.SIZE / Byte.SIZE);
        buffer.putLong(sourceMac);

        /* delete the flow entry to all the switches */
        for (IOFSwitch sw: macToSwitchPortMap.keySet()) {

            OFMatch match = new OFMatch();
            match.setDataLayerSource(buffer.array());

            /* set wildcards - we set only DL SRC port */
            match.setWildcards(
                ((Integer) sw.getAttribute(
                     IOFSwitch.PROP_FASTWILDCARDS)).intValue() &
                ~OFMatch.OFPFW_DL_SRC);

            // comment for debugging.
            /* Buggy !!!
            writeFlowMod (
                sw,
                OFFlowMod.OFPFC_ADD,
                (-1),
                match,
                OFPort.OFPP_NONE.getValue (),
                Hw1Switch.PRIORITY_DEFAULT);
            */
        }
    }

    /**
     * Adds a host to the MAC->SwitchPort mapping
     * @param sw The switch to add the mapping to
     * @param mac The MAC address of the host to add
     * @param portVal The switchport that the host is on
     */
    protected void addToPortMap(IOFSwitch sw, long mac, short portVal) {

        log.info("[@lfred] addToPortMap");

        Map<Long, Short> swMap = macToSwitchPortMap.get(sw);

        if (swMap == null) {
            // May be accessed by REST API so we need to make it thread safe
            swMap = Collections.synchronizedMap(new LRULinkedHashMap<Long, Short>(MAX_MACS_PER_SWITCH));
            macToSwitchPortMap.put(sw, swMap);
        }

        swMap.put(Long.valueOf(mac), Short.valueOf(portVal));
    }

    /**
     * Removes a host from the MAC->SwitchPort mapping
     * @param sw The switch to remove the mapping from
     * @param mac The MAC address of the host to remove
     */
    protected void removeFromPortMap(IOFSwitch sw, long mac) {

        log.info("[@lfred] removeFromPortMap");

        Map<Long, Short> swMap = macToSwitchPortMap.get(sw);

        if (swMap != null) {
            if (swMap.get(Long.valueOf(mac)) != null) {
                swMap.remove(Long.valueOf(mac));
            }
        }
    }

    /**
     * Get the port that a MAC is associated with
     * @param sw The switch to get the mapping from
     * @param mac The MAC address to get
     * @return The port the host is on
     */
    public Short getFromPortMap(IOFSwitch sw, long mac) {

        log.info("[@lfred] getFromPortMap");

        Map<Long, Short> swMap = macToSwitchPortMap.get(sw);

        if (swMap != null)
            return swMap.get(Long.valueOf(mac));
        else
            return null;
    }

    /**
     * Writes a OFFlowMod to a switch.
     * @param sw The switch to write the flowmod to.
     * @param command The FlowMod actions (add, delete, etc).
     * @param bufferId The buffer ID if the switch has buffered the packet.
     * @param match The OFMatch structure to write.
     * @param outPort The switch port to output it to.
     */
    private void writeFlowMod(
        IOFSwitch sw,
        short command,
        int bufferId,
        OFMatch match,
        short outPort,
        short priority,
        List<OFAction> actions,
        int actLen) {

        OFFlowMod flowMod = (OFFlowMod) floodlightProvider.getOFMessageFactory().getMessage(OFType.FLOW_MOD);

        /* config the flow mod */
        flowMod.setMatch(match);
        flowMod.setCookie(Hw1Switch.HW1_SWITCH_COOKIE);
        flowMod.setCommand(command);
        flowMod.setIdleTimeout(Hw1Switch.IDLE_TIMEOUT_DEFAULT);
        flowMod.setHardTimeout(Hw1Switch.HARD_TIMEOUT_DEFAULT);
        flowMod.setPriority(priority);
        flowMod.setBufferId(bufferId);
        flowMod.setOutPort((command == OFFlowMod.OFPFC_DELETE) ? outPort : OFPort.OFPP_NONE.getValue());
        flowMod.setFlags((command == OFFlowMod.OFPFC_DELETE) ? 0 : (short) (1 << 0));    // OFPFF_SEND_FLOW_REM

        // set the ofp_action_header/out actions:
        if (actions == null) {
            flowMod.setActions(Arrays.asList((OFAction) new OFActionOutput(outPort, (short) 0xffff)));
            actLen = OFActionOutput.MINIMUM_LENGTH;
        } else {
            flowMod.setActions(actions);
        }

        if (log.isTraceEnabled()) {
            log.trace("{} {} flow mod {}",
                      new Object[] { sw, (command == OFFlowMod.OFPFC_DELETE) ? "deleting" : "adding", flowMod });
        }

        // setup length
        flowMod.setLength((short) (OFFlowMod.MINIMUM_LENGTH + actLen));

        // and write it out
        try {
            sw.write(flowMod, null);
        } catch (IOException e) {
            log.error("Failed to write {} to switch {}", new Object[] { flowMod, sw }, e);
        }
    }

    /**
     * Writes an OFPacketOut message to a switch.
     * @param sw The switch to write the PacketOut to.
     * @param packetInMessage The corresponding PacketIn.
     * @param egressPort The switchport to output the PacketOut.
     */
    private void writePacketOutForPacketIn(
        IOFSwitch sw,
        OFPacketIn packetInMessage,
        short egressPort,
        long newDestMac,
        int newDestIp,
        long newSrcMac,
        int newSrcIp) {

        OFPacketOut packetOutMessage =
            (OFPacketOut) floodlightProvider.getOFMessageFactory().getMessage(OFType.PACKET_OUT);
        short packetOutLength = (short) OFPacketOut.MINIMUM_LENGTH;

        // Set buffer_id, in_port, actions_len
        packetOutMessage.setBufferId(packetInMessage.getBufferId());
        packetOutMessage.setInPort(packetInMessage.getInPort());

        // set actions
        List<OFAction> actions = new ArrayList<OFAction>(5);
        int lenAction = 0;

        if (newDestMac != -1) {
            actions.add(new OFActionDataLayerDestination(Ethernet.toByteArray(newDestMac)));
            lenAction += OFActionDataLayer.MINIMUM_LENGTH;
        }

        if (newDestIp != -1) {
            actions.add(new OFActionNetworkLayerDestination(newDestIp));
            lenAction += OFActionNetworkLayerAddress.MINIMUM_LENGTH;
        }

        if (newSrcMac != -1) {
            actions.add(new OFActionDataLayerSource(Ethernet.toByteArray(newSrcMac)));
            lenAction += OFActionDataLayer.MINIMUM_LENGTH;
        }

        if (newSrcIp != -1) {
            actions.add(new OFActionNetworkLayerSource(newSrcIp));
            lenAction += OFActionNetworkLayerAddress.MINIMUM_LENGTH;
        }

        /* @lfred: set output port */
        actions.add(new OFActionOutput(egressPort, (short) 0));
        lenAction += OFActionOutput.MINIMUM_LENGTH;

        /* @lfred: set action lens */
        packetOutMessage.setActionsLength((short) lenAction);

        /* @lfred: attach the actions to the packet */
        packetOutMessage.setActions(actions);

        /* increment packetOutLength */
        packetOutLength += lenAction;

        // set data - only if buffer_id == -1
        if (packetInMessage.getBufferId() == OFPacketOut.BUFFER_ID_NONE) {
            byte[] packetData = packetInMessage.getPacketData();
            packetOutMessage.setPacketData(packetData);
            packetOutLength += (short) packetData.length;
        }

        // finally, set the total length
        packetOutMessage.setLength(packetOutLength);

        // and write it to the switch
        try {
            sw.write(packetOutMessage, null);
        } catch (IOException e) {
            log.error("Failed to write {} to switch {}: {}", new Object[] { packetOutMessage, sw, e });
        }
    }

    /**
     * Processes a OFPacketIn message. If the switch has learned the MAC to port mapping
     * for the pair it will write a FlowMod for. If the mapping has not been learned the
     * we will flood the packet.
     * @param sw
     * @param pi
     * @param cntx
     * @return
     */
    private Command processPacketInMessage(
        IOFSwitch sw, OFPacketIn pi, FloodlightContext cntx) {

        Short inPort = Short.valueOf(pi.getInPort());
        OFMatch match = new OFMatch();

        match.loadFromPacket(pi.getPacketData(), inPort.shortValue());
        byte nwProtocol = match.getNetworkProtocol();
        Long sourceMac = Ethernet.toLong(match.getDataLayerSource());
        Long destMac = Ethernet.toLong(match.getDataLayerDestination());
        long now = System.currentTimeMillis();
        boolean switchSrcAddr = false, switchDstAddr = false, isNWPacket = true;

        /* handle the arp packet: allow ARP to be sent */
        if (match.getDataLayerType() == 0x0806) {
            writePacketOutForPacketIn(sw, pi, OFPort.OFPP_FLOOD.getValue(), -1, -1, -1, -1);
            return Command.CONTINUE;
        }

        /* @lfred: we process only NW layer packets */
        /* 0x01: ICMP, 0x06: TCP, 0x11: UDP */
        if (nwProtocol != 0x01 && nwProtocol != 0x06 && nwProtocol != 0x11) {
            isNWPacket = false;
            writePacketOutForPacketIn(sw, pi, OFPort.OFPP_FLOOD.getValue(), -1, -1, -1, -1);
            return Command.CONTINUE;
        }

        /* Block Blacklist */
        agingBlackList(now);
        if (isInBlackList(sourceMac.longValue(), now)) {
            log.info("[@lfred] @ rejected: backlist");
            return Command.CONTINUE;
        }

        /* load balancing */
        int destIp = match.getNetworkDestination(), srcIp = match.getNetworkSource();
        long svrSrcMac;

        if (SvrLoadBalance) {

            long tmpSrcMac = isAddrWebSvr(srcIp), tmpDstMac = isAddrWebSvr(destIp);
            if (!(tmpSrcMac != -1 && tmpDstMac != -1) &&
                !(tmpSrcMac == -1 && tmpDstMac == -1)) {

                /* @lfred: if going to web server, change the dst Mac and dst IP */
                if (destIp == m_webSvrIp) {
                    long newDstMac = findLeastLoadingMachine();

                    if (newDstMac != destMac.longValue()) {
                        log.info("[@lfred] Doing load-balancing. Switching to " + newDstMac);
                        destMac = Long.valueOf(newDstMac);
                        destIp = m_webSvr.get(Long.valueOf(newDstMac));
                        switchDstAddr = true;
                    }
                }

                if (tmpSrcMac != -1) { /* @lfred: deal with data sent from server */
                    sourceMac = Long.valueOf(tmpSrcMac);
                    srcIp  = m_webSvrIp;
                    switchSrcAddr = true;
                }
            }
        }

        /* Connection Cnt */
        Map<Long, Long> cnt = m_hostConnCnt.get(sourceMac);
        
        if (cnt != null) {
            if (cnt.size() > MAX_DESTINATION_NUMBER) {
                blockHost(sourceMac, now);
                cnt.clear();
                return Command.CONTINUE;
            }
    
            Long x = cnt.get(destMac);
            if (x != null)
                cnt.put(destMac, Long.valueOf(x.longValue() + 1));
            else
                cnt.put(destMac, Long.valueOf(Long.valueOf(1)));
        } else {
            cnt = new ConcurrentHashMap<Long, Long>();
            cnt.put(destMac, Long.valueOf(1));
            m_hostConnCnt.put(sourceMac, cnt);
        }

        /* Learning Switch */
        Map<Long, Short> swMap = macToSwitchPortMap.get(sw);
        if (swMap == null) { /* implement LEARNING SWITCH */
            swMap = Collections.synchronizedMap(new LRULinkedHashMap<Long, Short>(MAX_MACS_PER_SWITCH));
            macToSwitchPortMap.put(sw, swMap);
        }

        if (swMap.get(sourceMac) == null) {
            swMap.put(sourceMac, inPort);
        } else {
            if (swMap.get(sourceMac).longValue() != inPort)
                log.info("[@lfred] Port has been changed !? " + sourceMac);
        }

        /* Install Rule */
        Short outPort = swMap.get(destMac);
        if (outPort == null) {
            long smac = -1, dmac = -1;
            int sip = -1, dip = -1;

            if (switchDstAddr) {
                dmac = destMac.longValue();
                dip = destIp;
            }
            if (switchSrcAddr) {
                smac = sourceMac.longValue();
                sip = srcIp;
            }
            writePacketOutForPacketIn(sw, pi, OFPort.OFPP_FLOOD.getValue(), dmac, dip, smac, sip);
        } else if (outPort == match.getInputPort()) {
            log.info("[@lfred] packet ignored");
        } else {
            match.setWildcards(
                ((Integer) sw.getAttribute(
                     IOFSwitch.PROP_FASTWILDCARDS)).intValue() & ~OFMatch.OFPFW_IN_PORT & ~OFMatch.OFPFW_DL_SRC & ~OFMatch.OFPFW_DL_DST & ~OFMatch.OFPFW_NW_SRC_MASK & ~OFMatch.OFPFW_NW_DST_MASK);
            if (!switchSrcAddr && !switchDstAddr) {
                log.info("[@lfred] insert rules in the switch");
                writeFlowMod(sw, OFFlowMod.OFPFC_ADD, pi.getBufferId(), match, outPort.shortValue(), Hw1Switch.PRIORITY_DEFAULT, null, 0);
            } else {
                log.info("[@lfred] LOAD-BALANCING: insert rules in the switch");
                Vector<OFAction> actions = new Vector<OFAction>();
                short actLen = 0;

                if (switchDstAddr) {
                    actions.add(new OFActionDataLayerDestination(Ethernet.toByteArray(destMac.longValue())));
                    actLen += OFActionDataLayer.MINIMUM_LENGTH;
                    actions.add(new OFActionNetworkLayerDestination(destIp));
                    actLen += OFActionNetworkLayerAddress.MINIMUM_LENGTH;
                }
                if (switchSrcAddr) {
                    actions.add(new OFActionDataLayerSource(Ethernet.toByteArray(sourceMac.longValue())));
                    actLen += OFActionDataLayer.MINIMUM_LENGTH;
                    actions.add(new OFActionNetworkLayerSource(srcIp));
                    actLen += OFActionNetworkLayerAddress.MINIMUM_LENGTH;
                }
                actions.add(new OFActionOutput(outPort, (short) 0xffff));
                actLen += OFActionOutput.MINIMUM_LENGTH;
                writeFlowMod(sw, OFFlowMod.OFPFC_ADD, pi.getBufferId(), match, outPort.shortValue(), Hw1Switch.PRIORITY_DEFAULT, actions.subList(0, actions.size()), actLen);
            }
        }
        return Command.CONTINUE;
    }

    /**
     * Processes a flow removed message.
     * @param sw The switch that sent the flow removed message.
     * @param flowRemovedMessage The flow removed message.
     * @return Whether to continue processing this message or stop.
     */
    private Command processFlowRemovedMessage(
        IOFSwitch sw,
        OFFlowRemoved flowRemovedMessage) {

        if (flowRemovedMessage.getCookie() != Hw1Switch.HW1_SWITCH_COOKIE)
            return Command.CONTINUE;

        if (flowRemovedMessage.getReason() == OFFlowRemoved.OFFlowRemovedReason.OFPRR_DELETE) {
            log.info("[@lfred] flow removed successfully.");
            return Command.CONTINUE;
        }

        long now = System.currentTimeMillis();
        Long sourceMac = Ethernet.toLong(flowRemovedMessage.getMatch().getDataLayerSource());
        Long destMac = Ethernet.toLong(flowRemovedMessage.getMatch().getDataLayerDestination());

        log.info("[@lfred] processFlowRemovedMessage : " +
                 Long.toHexString(sourceMac.longValue()) + ":" +
                 Long.toHexString(destMac.longValue()));

        if (log.isTraceEnabled())
            log.trace("{} flow entry removed {}", sw, flowRemovedMessage);

        /**********************************************************************/
        /*                         Aging the BL                               */
        /**********************************************************************/
        /* updating & aging the black list */
        agingBlackList(now);

        /**********************************************************************/
        /*                         decrement Lnk Cnt                          */
        /**********************************************************************/
        /* reduce the link counter */
        Map<Long, Long> cnt = m_hostConnCnt.get(sourceMac);

        if (cnt != null) {
            if (cnt.get(destMac) != null) {
                long c = cnt.get(destMac).longValue();
                
                if (c == 1)
                    cnt.remove(destMac);
                else
                    cnt.put(destMac, Long.valueOf(c - 1));
                
                if (cnt.isEmpty()) 
                    m_hostConnCnt.remove(sourceMac);
            }
        } else
            log.info("[@lfred] asynchronous - ignored");

        /**********************************************************************/
        /*                       elephant flow handling                       */
        /**********************************************************************/
        /* get the number of bytes of this flow */
        long totalByteCount = flowRemovedMessage.getByteCount();
        Map<Long, Long> elephantCnt = m_elephantFlowCnt.get(sw);

        /* one elephant flow is found */
        if (totalByteCount > ELEPHANT_FLOW_BAND_WIDTH * HARD_TIMEOUT_DEFAULT) {

            log.info("[@lfred] elephant flow found: total byte: " + totalByteCount);

            if (elephantCnt == null) {
                /* the sourceMac has not yet been dtected */
                elephantCnt =
                    Collections.synchronizedMap(
                        new LRULinkedHashMap<Long, Long>(MAX_MACS_PER_SWITCH));

                m_elephantFlowCnt.put(sw, elephantCnt);
            }

            /* Maybe we should not do aging ? */
            /*
            else {
                // aging the flow table - remove the bad flows
                java.util.Iterator<Map.Entry<Long, Long>> iter = elephantCnt.entrySet().iterator();

                while (iter.hasNext()) {
                    Map.Entry<Long, Long> entry = iter.next();
                    if (now - entry.getValue() > FIREWALL_BLOCK_TIME_DUR) {
                        iter.remove();
                    }
                }
            }
            */

            /* record the elephant flow */
            elephantCnt.put(sourceMac, Long.valueOf(now));

            /* check if we need to block bad guys */
            if (elephantCnt.size() > MAX_ELEPHANT_FLOW_NUMBER) {

                log.info("[@lfred] elephant flow count reached");

                /* block all host */
                for (Map.Entry<Long, Long> entry : elephantCnt.entrySet()) {
                    blockHost(entry.getKey().longValue(), now);
                }

                /* clear all entries - because they are punished already. */
                elephantCnt.clear();
            }

            /* record the elephant flow if going to the web servers */
            if (m_webSvr.get(destMac) != null) {
                m_svrStats.put(
                    destMac,
                    Long.valueOf(m_svrStats.get(destMac).longValue() + 1));

                log.info("[@lfred] Update web server load: " + destMac + ":" + m_svrStats.get(destMac));
            }
        }

        return Command.CONTINUE;
    }

    // IOFMessageListener
    @Override
    public Command receive(
        IOFSwitch sw,
        OFMessage msg,
        FloodlightContext cntx) {

        switch (msg.getType()) {

        case PACKET_IN:
            return this.processPacketInMessage(sw, (OFPacketIn) msg, cntx);

        case FLOW_REMOVED:
            return this.processFlowRemovedMessage(sw, (OFFlowRemoved) msg);

        case ERROR:
            log.info("received an error {} from switch {}", (OFError) msg, sw);
            return Command.CONTINUE;

        default:
            log.error("received an unexpected message {} from switch {}", msg, sw);
            break;
        }

        return Command.CONTINUE;
    }

    @Override
    public boolean isCallbackOrderingPrereq(OFType type, String name) {
        return false;
    }

    @Override
    public boolean isCallbackOrderingPostreq(OFType type, String name) {
        return false;
    }

    // IFloodlightModule
    @Override
    public Collection<Class<? extends IFloodlightService>> getModuleServices() {

        Collection<Class<? extends IFloodlightService>> l =
            new ArrayList<Class<? extends IFloodlightService>>();
        return l;

    }

    @Override
    public Map<Class<? extends IFloodlightService>, IFloodlightService> getServiceImpls() {

        Map<Class<? extends IFloodlightService>, IFloodlightService> m =
            new HashMap<Class<? extends IFloodlightService>, IFloodlightService>();

        return m;
    }

    @Override
    public Collection<Class<? extends IFloodlightService>> getModuleDependencies() {

        Collection<Class<? extends IFloodlightService>> l =
            new ArrayList<Class<? extends IFloodlightService>>();

        l.add(IFloodlightProviderService.class);
        return l;
    }

    @Override
    public void init(FloodlightModuleContext context)
    throws FloodlightModuleException {

        /* get flood light instance */
        floodlightProvider =
            context.getServiceImpl(IFloodlightProviderService.class);

        /* instantiate the port map */
        macToSwitchPortMap = new ConcurrentHashMap<IOFSwitch, Map<Long, Short>>();

        /* instantiate the elephant flow counter */
        m_elephantFlowCnt = new ConcurrentHashMap<IOFSwitch, Map<Long, Long>>();

        /* instantiate the connection counter */
        m_hostConnCnt = new ConcurrentHashMap<Long, Map<Long, Long>>();

        /* instantiate the blacklist */
        blacklist = new ConcurrentHashMap<Long, Long>();

        /* web server loading stats <MAC, IP> */
        m_webSvr = new ConcurrentHashMap<Long, Integer>();

        /* web server loading stats <Mac, data count> */
        m_svrStats = new ConcurrentHashMap<Long, Long>();

        initWebSvrs();
    }

    /* @lfred: find the web server with smallest load */
    protected long findLeastLoadingMachine() {

        long minLoad = Long.MAX_VALUE;
        long minMac = Long.MAX_VALUE;

        for (Map.Entry<Long, Long> entry : m_svrStats.entrySet()) {

            log.info("   [@lfred] svr loading " + entry.getKey() + ":" + entry.getValue());

            if (entry.getValue().longValue() < minLoad) {
                minLoad = entry.getValue().longValue();
                minMac = entry.getKey().longValue();
            }
        }

        log.info("[@lfred] the machine with min loading is " + minMac);
        return minMac;
    }

    /* @lfred: check if an specific ip is one of the web server */
    protected long isAddrWebSvr(int ip) {

        for (Map.Entry<Long, Integer> entry : m_webSvr.entrySet()) {

            if (entry.getValue().intValue() == ip) {
                return entry.getKey().longValue();
            }
        }

        return -1;
    }

    /* @lfred: the function is used to initialize the web server addressed and accounts */
    protected void initWebSvrs() {
        SvrLoadBalance = false;
        m_webSvrIp = IPv4.toIPv4Address(new String("10.0.0.1"));
        m_webSvr.put(Long.valueOf(1), IPv4.toIPv4Address(new String("10.0.0.1")));
        m_webSvr.put(Long.valueOf(2), IPv4.toIPv4Address(new String("10.0.0.2")));
        m_svrStats.put(Long.valueOf(1), Long.valueOf(0));
        m_svrStats.put(Long.valueOf(2), Long.valueOf(0));
    }

    @Override
    public void startUp(FloodlightModuleContext context) {
        floodlightProvider.addOFMessageListener(OFType.PACKET_IN, this);
        floodlightProvider.addOFMessageListener(OFType.FLOW_REMOVED, this);
        floodlightProvider.addOFMessageListener(OFType.ERROR, this);
    }
}
