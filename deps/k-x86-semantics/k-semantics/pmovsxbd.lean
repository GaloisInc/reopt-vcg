def pmovsxbd : instruction :=
  definst "pmovsxbd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 4;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      let v_8 <- eval (concat (sext v_6 32) (sext v_7 32));
      let v_9 <- eval (concat (sext v_5 32) v_8);
      let v_10 <- eval (concat (sext v_4 32) v_9);
      setRegister (lhs.of_reg xmm_1) v_10;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 96 104);
      let (v_4 : expression (bv 8)) <- eval (extract v_2 104 112);
      let (v_5 : expression (bv 8)) <- eval (extract v_2 112 120);
      let (v_6 : expression (bv 8)) <- eval (extract v_2 120 128);
      let v_7 <- eval (concat (sext v_5 32) (sext v_6 32));
      let v_8 <- eval (concat (sext v_4 32) v_7);
      let v_9 <- eval (concat (sext v_3 32) v_8);
      setRegister (lhs.of_reg xmm_1) v_9;
      pure ()
     action
