def phminposuw : instruction :=
  definst "phminposuw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_6 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_8 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_12 <- eval (ult v_10 v_11);
      let v_13 <- eval (mux v_12 v_10 v_11);
      let v_14 <- eval (ult v_9 v_13);
      let v_15 <- eval (mux v_14 v_9 v_13);
      let v_16 <- eval (ult v_8 v_15);
      let v_17 <- eval (mux v_16 v_8 v_15);
      let v_18 <- eval (ult v_7 v_17);
      let v_19 <- eval (mux v_18 v_7 v_17);
      let v_20 <- eval (ult v_6 v_19);
      let v_21 <- eval (mux v_20 v_6 v_19);
      let v_22 <- eval (ult v_5 v_21);
      let v_23 <- eval (mux v_22 v_5 v_21);
      let v_24 <- eval (ult v_4 v_23);
      let v_25 <- eval (concat (mux v_24 (expression.bv_nat 112 7) (mux v_22 (expression.bv_nat 112 6) (mux v_20 (expression.bv_nat 112 5) (mux v_18 (expression.bv_nat 112 4) (mux v_16 (expression.bv_nat 112 3) (mux v_14 (expression.bv_nat 112 2) (mux v_12 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_24 v_4 v_23));
      setRegister (lhs.of_reg xmm_1) v_25;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let (v_4 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_5 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_7 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_8 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_11 <- eval (ult v_9 v_10);
      let v_12 <- eval (mux v_11 v_9 v_10);
      let v_13 <- eval (ult v_8 v_12);
      let v_14 <- eval (mux v_13 v_8 v_12);
      let v_15 <- eval (ult v_7 v_14);
      let v_16 <- eval (mux v_15 v_7 v_14);
      let v_17 <- eval (ult v_6 v_16);
      let v_18 <- eval (mux v_17 v_6 v_16);
      let v_19 <- eval (ult v_5 v_18);
      let v_20 <- eval (mux v_19 v_5 v_18);
      let v_21 <- eval (ult v_4 v_20);
      let v_22 <- eval (mux v_21 v_4 v_20);
      let v_23 <- eval (ult v_3 v_22);
      let v_24 <- eval (concat (mux v_23 (expression.bv_nat 112 7) (mux v_21 (expression.bv_nat 112 6) (mux v_19 (expression.bv_nat 112 5) (mux v_17 (expression.bv_nat 112 4) (mux v_15 (expression.bv_nat 112 3) (mux v_13 (expression.bv_nat 112 2) (mux v_11 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_23 v_3 v_22));
      setRegister (lhs.of_reg xmm_1) v_24;
      pure ()
     action
