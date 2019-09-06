def vextractf1281 : instruction :=
  definst "vextractf128" $ do
    pattern fun (v_2475 : imm int) (v_2479 : reg (bv 256)) (v_2474 : reg (bv 128)) => do
      v_4092 <- getRegister v_2479;
      setRegister (lhs.of_reg v_2474) (mux (isBitClear (handleImmediateWithSignExtend v_2475 8 8) 7) (extract v_4092 128 256) (extract v_4092 0 128));
      pure ()
    pat_end;
    pattern fun (v_2470 : imm int) (v_2473 : reg (bv 256)) (v_2469 : Mem) => do
      v_13848 <- evaluateAddress v_2469;
      v_13851 <- getRegister v_2473;
      store v_13848 (mux (isBitClear (handleImmediateWithSignExtend v_2470 8 8) 7) (extract v_13851 128 256) (extract v_13851 0 128)) 16;
      pure ()
    pat_end
