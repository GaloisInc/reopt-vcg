def vcvtsi2ssl : instruction :=
  definst "vcvtsi2ssl" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 4;
      let v_7 <- eval (concat v_4 (fp_bitcast_to_bv (Int2Float (svalueMInt v_6) 24 8) 32));
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let v_5 <- getRegister (lhs.of_reg r32_0);
      let v_6 <- eval (concat v_4 (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 24 8) 32));
      setRegister (lhs.of_reg xmm_2) v_6;
      pure ()
     action
