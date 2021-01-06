def movlhps : instruction :=
  definst "movlhps" $ do
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 64 128);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_6 <- eval (concat v_3 v_5);
      setRegister (lhs.of_reg xmm_1) v_6;
      pure ()
     action
