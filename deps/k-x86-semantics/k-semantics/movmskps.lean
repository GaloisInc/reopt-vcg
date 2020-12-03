def movmskps : instruction :=
  definst "movmskps" $ do
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_5 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_6 : expression (bv 1)) <- eval (extract v_2 96 97);
      let v_7 <- eval (concat v_5 v_6);
      let v_8 <- eval (concat v_4 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat (expression.bv_nat 28 0) v_9);
      setRegister (lhs.of_reg r32_1) v_10;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 32 33);
      let (v_5 : expression (bv 1)) <- eval (extract v_2 64 65);
      let (v_6 : expression (bv 1)) <- eval (extract v_2 96 97);
      let v_7 <- eval (concat v_5 v_6);
      let v_8 <- eval (concat v_4 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat (expression.bv_nat 60 0) v_9);
      setRegister (lhs.of_reg r64_1) v_10;
      pure ()
     action
