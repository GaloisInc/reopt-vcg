def phaddd : instruction :=
  definst "phaddd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_8 <- eval (concat (add v_4 v_5) (add v_6 v_7));
      let v_9 <- getRegister (lhs.of_reg xmm_1);
      let (v_10 : expression (bv 32)) <- eval (extract v_9 0 32);
      let (v_11 : expression (bv 32)) <- eval (extract v_9 32 64);
      let v_12 <- eval (concat v_8 (add v_10 v_11));
      let (v_13 : expression (bv 32)) <- eval (extract v_9 64 96);
      let (v_14 : expression (bv 32)) <- eval (extract v_9 96 128);
      let v_15 <- eval (concat v_12 (add v_13 v_14));
      setRegister (lhs.of_reg xmm_1) v_15;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let (v_4 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_5 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_7 <- eval (concat (add v_3 v_4) (add v_5 v_6));
      let v_8 <- getRegister (lhs.of_reg xmm_1);
      let (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      let (v_10 : expression (bv 32)) <- eval (extract v_8 32 64);
      let v_11 <- eval (concat v_7 (add v_9 v_10));
      let (v_12 : expression (bv 32)) <- eval (extract v_8 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract v_8 96 128);
      let v_14 <- eval (concat v_11 (add v_12 v_13));
      setRegister (lhs.of_reg xmm_1) v_14;
      pure ()
     action
