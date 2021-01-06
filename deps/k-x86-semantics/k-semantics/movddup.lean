def movddup : instruction :=
  definst "movddup" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let v_4 <- eval (concat v_3 v_3);
      setRegister (lhs.of_reg xmm_1) v_4;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 64 128);
      let v_4 <- eval (concat v_3 v_3);
      setRegister (lhs.of_reg xmm_1) v_4;
      pure ()
     action
