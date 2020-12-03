def divss : instruction :=
  definst "divss" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 96)) <- eval (extract v_2 0 96);
      let (v_4 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 4;
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let v_9 <- eval (concat v_3 (fp_bitcast_to_bv (fp_div v_5 v_8) 32));
      setRegister (lhs.of_reg xmm_1) v_9;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 96)) <- eval (extract v_2 0 96);
      let (v_4 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- getRegister (lhs.of_reg xmm_0);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let v_9 <- eval (concat v_3 (fp_bitcast_to_bv (fp_div v_5 v_8) 32));
      setRegister (lhs.of_reg xmm_1) v_9;
      pure ()
     action
