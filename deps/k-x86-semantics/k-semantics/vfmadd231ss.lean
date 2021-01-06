def vfmadd231ss : instruction :=
  definst "vfmadd231ss" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      let v_8 <- evaluateAddress mem_0;
      let v_9 <- load v_8 4;
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      let v_13 <- eval (concat v_4 (fp_bitcast_to_bv (fp_add (fp_mul v_7 v_10) v_12) 32));
      setRegister (lhs.of_reg xmm_2) v_13;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      let v_8 <- getRegister (lhs.of_reg xmm_0);
      let (v_9 : expression (bv 32)) <- eval (extract v_8 96 128);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      let v_13 <- eval (concat v_4 (fp_bitcast_to_bv (fp_add (fp_mul v_7 v_10) v_12) 32));
      setRegister (lhs.of_reg xmm_2) v_13;
      pure ()
     action
