def cvtps2pd : instruction :=
  definst "cvtps2pd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- eval (fp_round float_class.fp64 v_5);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let v_9 <- eval (fp_round float_class.fp64 v_8);
      let v_10 <- eval (concat (fp_bitcast_to_bv v_6 64) (fp_bitcast_to_bv v_9 64));
      setRegister (lhs.of_reg xmm_1) v_10;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 64 96);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp32 v_3);
      let v_5 <- eval (fp_round float_class.fp64 v_4);
      let (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      let v_8 <- eval (fp_round float_class.fp64 v_7);
      let v_9 <- eval (concat (fp_bitcast_to_bv v_5 64) (fp_bitcast_to_bv v_8 64));
      setRegister (lhs.of_reg xmm_1) v_9;
      pure ()
     action
