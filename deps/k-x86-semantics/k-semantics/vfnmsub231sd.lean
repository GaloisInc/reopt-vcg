def vfnmsub231sd : instruction :=
  definst "vfnmsub231sd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      let v_7 <- eval (concat (expression.bv_nat 32 0) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_9 <- eval (concat (expression.bv_nat 32 0) v_8);
      let v_10 <- eval (concat (expression.bv_nat 32 0) (mux (eq (/- (_,_) -/  mincmp_double v_7 v_9) (expression.bv_nat 1 1)) v_6 v_8));
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      let (v_12 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp64 v_12);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_11 v_11)) v_13) 64));
      let v_15 <- evaluateAddress mem_0;
      let v_16 <- load v_15 8;
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp64 v_16);
      let (v_18 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp64 v_18);
      let v_20 <- eval (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul v_14 v_17) v_19) 64));
      setRegister (lhs.of_reg xmm_2) v_20;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      let v_7 <- eval (concat (expression.bv_nat 32 0) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_9 <- eval (concat (expression.bv_nat 32 0) v_8);
      let v_10 <- eval (concat (expression.bv_nat 32 0) (mux (eq (/- (_,_) -/  mincmp_double v_7 v_9) (expression.bv_nat 1 1)) v_6 v_8));
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      let (v_12 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp64 v_12);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_11 v_11)) v_13) 64));
      let v_15 <- getRegister (lhs.of_reg xmm_0);
      let (v_16 : expression (bv 64)) <- eval (extract v_15 64 128);
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp64 v_16);
      let (v_18 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp64 v_18);
      let v_20 <- eval (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul v_14 v_17) v_19) 64));
      setRegister (lhs.of_reg xmm_2) v_20;
      pure ()
     action
