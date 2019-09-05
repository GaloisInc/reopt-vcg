def vextractf1281 : instruction :=
  definst "vextractf128" $ do
    pattern fun (v_2449 : imm int) (v_2450 : reg (bv 256)) (v_2452 : reg (bv 128)) => do
      v_4065 <- getRegister v_2450;
      setRegister (lhs.of_reg v_2452) (mux (isBitClear (handleImmediateWithSignExtend v_2449 8 8) 7) (extract v_4065 128 256) (extract v_4065 0 128));
      pure ()
    pat_end;
    pattern fun (v_2445 : imm int) (v_2446 : reg (bv 256)) (v_2444 : Mem) => do
      v_13821 <- evaluateAddress v_2444;
      v_13824 <- getRegister v_2446;
      store v_13821 (mux (isBitClear (handleImmediateWithSignExtend v_2445 8 8) 7) (extract v_13824 128 256) (extract v_13824 0 128)) 16;
      pure ()
    pat_end
