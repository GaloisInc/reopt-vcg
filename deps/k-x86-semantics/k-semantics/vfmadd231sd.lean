def vfmadd231sd : instruction :=
  definst "vfmadd231sd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      let v_8 <- evaluateAddress mem_0;
      let v_9 <- load v_8 8;
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      let (v_11 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) v_12) 64));
      let v_14 <- eval (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul v_7 v_10) v_13) 64));
      setRegister (lhs.of_reg xmm_2) v_14;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      let v_8 <- getRegister (lhs.of_reg xmm_0);
      let (v_9 : expression (bv 64)) <- eval (extract v_8 64 128);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      let (v_11 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) v_12) 64));
      let v_14 <- eval (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul v_7 v_10) v_13) 64));
      setRegister (lhs.of_reg xmm_2) v_14;
      pure ()
     action
