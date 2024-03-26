using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace _33D03.Server
{
    internal class PipServer
    {
        private TxpServer txpServer;

        public PipServer(TxpServer txpServer)
        {
            this.txpServer = txpServer;
        }

        public void Start()
        {
            txpServer.OnPacketReceived += TxpServer_OnPacketReceived;
            txpServer.Start();
        }

        private void TxpServer_OnPacketReceived(TxpClientConversation clientconversation, byte[] data)
        {
            throw new NotImplementedException();
        }

        private void SendHello()
        {
        }
    }
}
