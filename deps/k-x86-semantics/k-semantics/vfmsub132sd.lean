def vfmsub132sd : instruction :=
  definst "vfmsub132sd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp64 v_5);
      let v_7 <- evaluateAddress mem_0;
      let v_8 <- load v_7 8;
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      let v_10 <- getRegister (lhs.of_reg xmm_1);
      let (v_11 : expression (bv 64)) <- eval (extract v_10 64 128);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      let v_13 <- eval (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul v_6 v_9) v_12) 64));
      setRegister (lhs.of_reg xmm_2) v_13;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp64 v_5);
      let v_7 <- getRegister (lhs.of_reg xmm_0);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 64 128);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      let v_10 <- getRegister (lhs.of_reg xmm_1);
      let (v_11 : expression (bv 64)) <- eval (extract v_10 64 128);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      let v_13 <- eval (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul v_6 v_9) v_12) 64));
      setRegister (lhs.of_reg xmm_2) v_13;
      pure ()
     action
