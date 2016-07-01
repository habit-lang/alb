-- ### High-level overview of IPC (incomplete, of course):

-- Entry point:

ipc :: SystemCall
ipc  = getCurrent >>= ipcSend

-- IPC send phase:

ipcSend :: Ref TCB -> SystemCall
ipcSend current
  = do to <- ipcGetTo current
       if to == nilThread then
         ipcRecv current
       else if<- sendMessage MRs current to then
         ipcRecv current
       else
         reschedule

-- IPC receive phase:

ipcRecv :: Ref TCB -> SystemCall
ipcRecv current
  = do fromSpec <- ipcGetFromSpec current
       if fromspec /= nilThread then
         set (current.utcb.mrs @ 0) 0
         recvMessage MRs current fromSpec
       reschedule



-- Stubs for lower-level functions mentioned above:

getCurrent         :: K (Ref TCB)
getCurrent          = getCurrent

ipcGetTo           :: Ref TCB -> K ThreadId
ipcGetTo tcb        = get tcb.context.regs.eax

ipcGetFromSpec     :: Ref TCB -> K ThreadId
ipcGetFromSpec tcb  = get tcb.context.regs.edx

