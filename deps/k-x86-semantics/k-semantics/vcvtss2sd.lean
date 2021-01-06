def vcvtss2sd : instruction :=
  definst "vcvtss2sd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 4;
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      let v_8 <- eval (fp_round float_class.fp64 v_7);
      let v_9 <- eval (concat v_4 (fp_bitcast_to_bv v_8 64));
      setRegister (lhs.of_reg xmm_2) v_9;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      let v_8 <- eval (fp_round float_class.fp64 v_7);
      let v_9 <- eval (concat v_4 (fp_bitcast_to_bv v_8 64));
      setRegister (lhs.of_reg xmm_2) v_9;
      pure ()
     action
