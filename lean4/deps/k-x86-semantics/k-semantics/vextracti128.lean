def vextracti1281 : instruction :=
  definst "vextracti128" $ do
    pattern fun (v_2460 : imm int) (v_2461 : reg (bv 256)) (v_2463 : reg (bv 128)) => do
      v_4077 <- getRegister v_2461;
      setRegister (lhs.of_reg v_2463) (mux (isBitClear (handleImmediateWithSignExtend v_2460 8 8) 7) (extract v_4077 128 256) (extract v_4077 0 128));
      pure ()
    pat_end;
    pattern fun (v_2456 : imm int) (v_2457 : reg (bv 256)) (v_2455 : Mem) => do
      v_13829 <- evaluateAddress v_2455;
      v_13832 <- getRegister v_2457;
      store v_13829 (mux (isBitClear (handleImmediateWithSignExtend v_2456 8 8) 7) (extract v_13832 128 256) (extract v_13832 0 128)) 16;
      pure ()
    pat_end
