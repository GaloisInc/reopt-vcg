def haddpd : instruction :=
  definst "haddpd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      let (v_6 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      let v_8 <- getRegister (lhs.of_reg xmm_1);
      let (v_9 : expression (bv 64)) <- eval (extract v_8 64 128);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      let (v_11 : expression (bv 64)) <- eval (extract v_8 0 64);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      let v_13 <- eval (concat (fp_bitcast_to_bv (fp_add v_5 v_7) 64) (fp_bitcast_to_bv (fp_add v_10 v_12) 64));
      setRegister (lhs.of_reg xmm_1) v_13;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 64 128);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp64 v_3);
      let (v_5 : expression (bv 64)) <- eval (extract v_2 0 64);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp64 v_5);
      let v_7 <- getRegister (lhs.of_reg xmm_1);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 64 128);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      let (v_10 : expression (bv 64)) <- eval (extract v_7 0 64);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      let v_12 <- eval (concat (fp_bitcast_to_bv (fp_add v_4 v_6) 64) (fp_bitcast_to_bv (fp_add v_9 v_11) 64));
      setRegister (lhs.of_reg xmm_1) v_12;
      pure ()
     action
