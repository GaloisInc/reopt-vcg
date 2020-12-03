def cvtsd2ss : instruction :=
  definst "cvtsd2ss" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 96)) <- eval (extract v_2 0 96);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 8;
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp64 v_5);
      let v_7 <- eval (concat v_3 (fp_bitcast_to_bv (fp_round v_6 24 8) 32));
      setRegister (lhs.of_reg xmm_1) v_7;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 96)) <- eval (extract v_2 0 96);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp64 v_5);
      let v_7 <- eval (concat v_3 (fp_bitcast_to_bv (fp_round v_6 24 8) 32));
      setRegister (lhs.of_reg xmm_1) v_7;
      pure ()
     action
