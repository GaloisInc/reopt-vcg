def vcvtps2pd : instruction :=
  definst "vcvtps2pd" $ do
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
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- eval (fp_round float_class.fp64 v_5);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let v_9 <- eval (fp_round float_class.fp64 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      let v_12 <- eval (fp_round float_class.fp64 v_11);
      let (v_13 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      let v_15 <- eval (fp_round float_class.fp64 v_14);
      let v_16 <- eval (concat (fp_bitcast_to_bv v_12 64) (fp_bitcast_to_bv v_15 64));
      let v_17 <- eval (concat (fp_bitcast_to_bv v_9 64) v_16);
      let v_18 <- eval (concat (fp_bitcast_to_bv v_6 64) v_17);
      setRegister (lhs.of_reg ymm_1) v_18;
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
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp32 v_3);
      let v_5 <- eval (fp_round float_class.fp64 v_4);
      let (v_6 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      let v_8 <- eval (fp_round float_class.fp64 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 64 96);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let v_11 <- eval (fp_round float_class.fp64 v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      let v_14 <- eval (fp_round float_class.fp64 v_13);
      let v_15 <- eval (concat (fp_bitcast_to_bv v_11 64) (fp_bitcast_to_bv v_14 64));
      let v_16 <- eval (concat (fp_bitcast_to_bv v_8 64) v_15);
      let v_17 <- eval (concat (fp_bitcast_to_bv v_5 64) v_16);
      setRegister (lhs.of_reg ymm_1) v_17;
      pure ()
     action
