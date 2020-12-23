def cvtpd2ps : instruction :=
  definst "cvtpd2ps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      let v_6 <- eval (fp_round float_class.fp32 v_5);
      let (v_7 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      let v_9 <- eval (fp_round float_class.fp32 v_8);
      let v_10 <- eval (concat (fp_bitcast_to_bv v_6 32) (fp_bitcast_to_bv v_9 32));
      let v_11 <- eval (concat (expression.bv_nat 64 0) v_10);
      setRegister (lhs.of_reg xmm_1) v_11;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp64 v_3);
      let v_5 <- eval (fp_round float_class.fp32 v_4);
      let (v_6 : expression (bv 64)) <- eval (extract v_2 64 128);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      let v_8 <- eval (fp_round float_class.fp32 v_7);
      let v_9 <- eval (concat (fp_bitcast_to_bv v_5 32) (fp_bitcast_to_bv v_8 32));
      let v_10 <- eval (concat (expression.bv_nat 64 0) v_9);
      setRegister (lhs.of_reg xmm_1) v_10;
      pure ()
     action
