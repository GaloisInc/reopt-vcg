def paddw : instruction :=
  definst "paddw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let (v_7 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_13 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_15 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_16 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_17 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_19 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_20 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_21 <- eval (concat (add v_17 v_18) (add v_19 v_20));
      let v_22 <- eval (concat (add v_15 v_16) v_21);
      let v_23 <- eval (concat (add v_13 v_14) v_22);
      let v_24 <- eval (concat (add v_11 v_12) v_23);
      let v_25 <- eval (concat (add v_9 v_10) v_24);
      let v_26 <- eval (concat (add v_7 v_8) v_25);
      let v_27 <- eval (concat (add v_3 v_6) v_26);
      setRegister (lhs.of_reg xmm_1) v_27;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_7 : expression (bv 16)) <- eval (extract v_4 16 32);
      let (v_8 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_9 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_13 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_14 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_15 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_16 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_17 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_18 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_19 : expression (bv 16)) <- eval (extract v_4 112 128);
      let v_20 <- eval (concat (add v_16 v_17) (add v_18 v_19));
      let v_21 <- eval (concat (add v_14 v_15) v_20);
      let v_22 <- eval (concat (add v_12 v_13) v_21);
      let v_23 <- eval (concat (add v_10 v_11) v_22);
      let v_24 <- eval (concat (add v_8 v_9) v_23);
      let v_25 <- eval (concat (add v_6 v_7) v_24);
      let v_26 <- eval (concat (add v_3 v_5) v_25);
      setRegister (lhs.of_reg xmm_1) v_26;
      pure ()
     action
