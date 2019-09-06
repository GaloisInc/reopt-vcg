def vextracti1281 : instruction :=
  definst "vextracti128" $ do
    pattern fun (v_2486 : imm int) (v_2490 : reg (bv 256)) (v_2485 : reg (bv 128)) => do
      v_4104 <- getRegister v_2490;
      setRegister (lhs.of_reg v_2485) (mux (isBitClear (handleImmediateWithSignExtend v_2486 8 8) 7) (extract v_4104 128 256) (extract v_4104 0 128));
      pure ()
    pat_end;
    pattern fun (v_2481 : imm int) (v_2484 : reg (bv 256)) (v_2480 : Mem) => do
      v_13856 <- evaluateAddress v_2480;
      v_13859 <- getRegister v_2484;
      store v_13856 (mux (isBitClear (handleImmediateWithSignExtend v_2481 8 8) 7) (extract v_13859 128 256) (extract v_13859 0 128)) 16;
      pure ()
    pat_end
