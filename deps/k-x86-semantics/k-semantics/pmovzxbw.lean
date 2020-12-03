def pmovzxbw : instruction :=
  definst "pmovzxbw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_10 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 56 64);
      let v_12 <- eval (concat (expression.bv_nat 8 0) v_11);
      let v_13 <- eval (concat v_10 v_12);
      let v_14 <- eval (concat (expression.bv_nat 8 0) v_13);
      let v_15 <- eval (concat v_9 v_14);
      let v_16 <- eval (concat (expression.bv_nat 8 0) v_15);
      let v_17 <- eval (concat v_8 v_16);
      let v_18 <- eval (concat (expression.bv_nat 8 0) v_17);
      let v_19 <- eval (concat v_7 v_18);
      let v_20 <- eval (concat (expression.bv_nat 8 0) v_19);
      let v_21 <- eval (concat v_6 v_20);
      let v_22 <- eval (concat (expression.bv_nat 8 0) v_21);
      let v_23 <- eval (concat v_5 v_22);
      let v_24 <- eval (concat (expression.bv_nat 8 0) v_23);
      let v_25 <- eval (concat v_4 v_24);
      let v_26 <- eval (concat (expression.bv_nat 8 0) v_25);
      setRegister (lhs.of_reg xmm_1) v_26;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 64 72);
      let (v_4 : expression (bv 8)) <- eval (extract v_2 72 80);
      let (v_5 : expression (bv 8)) <- eval (extract v_2 80 88);
      let (v_6 : expression (bv 8)) <- eval (extract v_2 88 96);
      let (v_7 : expression (bv 8)) <- eval (extract v_2 96 104);
      let (v_8 : expression (bv 8)) <- eval (extract v_2 104 112);
      let (v_9 : expression (bv 8)) <- eval (extract v_2 112 120);
      let (v_10 : expression (bv 8)) <- eval (extract v_2 120 128);
      let v_11 <- eval (concat (expression.bv_nat 8 0) v_10);
      let v_12 <- eval (concat v_9 v_11);
      let v_13 <- eval (concat (expression.bv_nat 8 0) v_12);
      let v_14 <- eval (concat v_8 v_13);
      let v_15 <- eval (concat (expression.bv_nat 8 0) v_14);
      let v_16 <- eval (concat v_7 v_15);
      let v_17 <- eval (concat (expression.bv_nat 8 0) v_16);
      let v_18 <- eval (concat v_6 v_17);
      let v_19 <- eval (concat (expression.bv_nat 8 0) v_18);
      let v_20 <- eval (concat v_5 v_19);
      let v_21 <- eval (concat (expression.bv_nat 8 0) v_20);
      let v_22 <- eval (concat v_4 v_21);
      let v_23 <- eval (concat (expression.bv_nat 8 0) v_22);
      let v_24 <- eval (concat v_3 v_23);
      let v_25 <- eval (concat (expression.bv_nat 8 0) v_24);
      setRegister (lhs.of_reg xmm_1) v_25;
      pure ()
     action
