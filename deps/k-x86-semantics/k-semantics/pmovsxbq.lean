def pmovsxbq : instruction :=
  definst "pmovsxbq" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 2;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      let v_6 <- eval (concat (sext v_4 64) (sext v_5 64));
      setRegister (lhs.of_reg xmm_1) v_6;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 112 120);
      let (v_4 : expression (bv 8)) <- eval (extract v_2 120 128);
      let v_5 <- eval (concat (sext v_3 64) (sext v_4 64));
      setRegister (lhs.of_reg xmm_1) v_5;
      pure ()
     action
