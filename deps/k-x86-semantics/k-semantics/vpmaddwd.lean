def vpmaddwd : instruction :=
  definst "vpmaddwd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 16)) <- eval (extract v_4 16 32);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 16 32);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 0 16);
      let (v_9 : expression (bv 16)) <- eval (extract v_6 0 16);
      let (v_10 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_6 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_13 : expression (bv 16)) <- eval (extract v_6 32 48);
      let (v_14 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_15 : expression (bv 16)) <- eval (extract v_6 80 96);
      let (v_16 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_17 : expression (bv 16)) <- eval (extract v_6 64 80);
      let (v_18 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_19 : expression (bv 16)) <- eval (extract v_6 112 128);
      let (v_20 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_21 : expression (bv 16)) <- eval (extract v_6 96 112);
      let v_22 <- eval (concat (add (mul (sext v_14 32) (sext v_15 32)) (mul (sext v_16 32) (sext v_17 32))) (add (mul (sext v_18 32) (sext v_19 32)) (mul (sext v_20 32) (sext v_21 32))));
      let v_23 <- eval (concat (add (mul (sext v_10 32) (sext v_11 32)) (mul (sext v_12 32) (sext v_13 32))) v_22);
      let v_24 <- eval (concat (add (mul (sext v_5 32) (sext v_7 32)) (mul (sext v_8 32) (sext v_9 32))) v_23);
      setRegister (lhs.of_reg xmm_2) v_24;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 32;
      let (v_5 : expression (bv 16)) <- eval (extract v_4 16 32);
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 16 32);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 0 16);
      let (v_9 : expression (bv 16)) <- eval (extract v_6 0 16);
      let (v_10 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_6 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_13 : expression (bv 16)) <- eval (extract v_6 32 48);
      let (v_14 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_15 : expression (bv 16)) <- eval (extract v_6 80 96);
      let (v_16 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_17 : expression (bv 16)) <- eval (extract v_6 64 80);
      let (v_18 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_19 : expression (bv 16)) <- eval (extract v_6 112 128);
      let (v_20 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_21 : expression (bv 16)) <- eval (extract v_6 96 112);
      let (v_22 : expression (bv 16)) <- eval (extract v_4 144 160);
      let (v_23 : expression (bv 16)) <- eval (extract v_6 144 160);
      let (v_24 : expression (bv 16)) <- eval (extract v_4 128 144);
      let (v_25 : expression (bv 16)) <- eval (extract v_6 128 144);
      let (v_26 : expression (bv 16)) <- eval (extract v_4 176 192);
      let (v_27 : expression (bv 16)) <- eval (extract v_6 176 192);
      let (v_28 : expression (bv 16)) <- eval (extract v_4 160 176);
      let (v_29 : expression (bv 16)) <- eval (extract v_6 160 176);
      let (v_30 : expression (bv 16)) <- eval (extract v_4 208 224);
      let (v_31 : expression (bv 16)) <- eval (extract v_6 208 224);
      let (v_32 : expression (bv 16)) <- eval (extract v_4 192 208);
      let (v_33 : expression (bv 16)) <- eval (extract v_6 192 208);
      let (v_34 : expression (bv 16)) <- eval (extract v_4 240 256);
      let (v_35 : expression (bv 16)) <- eval (extract v_6 240 256);
      let (v_36 : expression (bv 16)) <- eval (extract v_4 224 240);
      let (v_37 : expression (bv 16)) <- eval (extract v_6 224 240);
      let v_38 <- eval (concat (add (mul (sext v_30 32) (sext v_31 32)) (mul (sext v_32 32) (sext v_33 32))) (add (mul (sext v_34 32) (sext v_35 32)) (mul (sext v_36 32) (sext v_37 32))));
      let v_39 <- eval (concat (add (mul (sext v_26 32) (sext v_27 32)) (mul (sext v_28 32) (sext v_29 32))) v_38);
      let v_40 <- eval (concat (add (mul (sext v_22 32) (sext v_23 32)) (mul (sext v_24 32) (sext v_25 32))) v_39);
      let v_41 <- eval (concat (add (mul (sext v_18 32) (sext v_19 32)) (mul (sext v_20 32) (sext v_21 32))) v_40);
      let v_42 <- eval (concat (add (mul (sext v_14 32) (sext v_15 32)) (mul (sext v_16 32) (sext v_17 32))) v_41);
      let v_43 <- eval (concat (add (mul (sext v_10 32) (sext v_11 32)) (mul (sext v_12 32) (sext v_13 32))) v_42);
      let v_44 <- eval (concat (add (mul (sext v_5 32) (sext v_7 32)) (mul (sext v_8 32) (sext v_9 32))) v_43);
      setRegister (lhs.of_reg ymm_2) v_44;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 0 16);
      let (v_8 : expression (bv 16)) <- eval (extract v_5 0 16);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 112 128);
      let (v_19 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_20 : expression (bv 16)) <- eval (extract v_5 96 112);
      let v_21 <- eval (concat (add (mul (sext v_13 32) (sext v_14 32)) (mul (sext v_15 32) (sext v_16 32))) (add (mul (sext v_17 32) (sext v_18 32)) (mul (sext v_19 32) (sext v_20 32))));
      let v_22 <- eval (concat (add (mul (sext v_9 32) (sext v_10 32)) (mul (sext v_11 32) (sext v_12 32))) v_21);
      let v_23 <- eval (concat (add (mul (sext v_4 32) (sext v_6 32)) (mul (sext v_7 32) (sext v_8 32))) v_22);
      setRegister (lhs.of_reg xmm_2) v_23;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_0);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 0 16);
      let (v_8 : expression (bv 16)) <- eval (extract v_5 0 16);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 112 128);
      let (v_19 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_20 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_21 : expression (bv 16)) <- eval (extract v_3 144 160);
      let (v_22 : expression (bv 16)) <- eval (extract v_5 144 160);
      let (v_23 : expression (bv 16)) <- eval (extract v_3 128 144);
      let (v_24 : expression (bv 16)) <- eval (extract v_5 128 144);
      let (v_25 : expression (bv 16)) <- eval (extract v_3 176 192);
      let (v_26 : expression (bv 16)) <- eval (extract v_5 176 192);
      let (v_27 : expression (bv 16)) <- eval (extract v_3 160 176);
      let (v_28 : expression (bv 16)) <- eval (extract v_5 160 176);
      let (v_29 : expression (bv 16)) <- eval (extract v_3 208 224);
      let (v_30 : expression (bv 16)) <- eval (extract v_5 208 224);
      let (v_31 : expression (bv 16)) <- eval (extract v_3 192 208);
      let (v_32 : expression (bv 16)) <- eval (extract v_5 192 208);
      let (v_33 : expression (bv 16)) <- eval (extract v_3 240 256);
      let (v_34 : expression (bv 16)) <- eval (extract v_5 240 256);
      let (v_35 : expression (bv 16)) <- eval (extract v_3 224 240);
      let (v_36 : expression (bv 16)) <- eval (extract v_5 224 240);
      let v_37 <- eval (concat (add (mul (sext v_29 32) (sext v_30 32)) (mul (sext v_31 32) (sext v_32 32))) (add (mul (sext v_33 32) (sext v_34 32)) (mul (sext v_35 32) (sext v_36 32))));
      let v_38 <- eval (concat (add (mul (sext v_25 32) (sext v_26 32)) (mul (sext v_27 32) (sext v_28 32))) v_37);
      let v_39 <- eval (concat (add (mul (sext v_21 32) (sext v_22 32)) (mul (sext v_23 32) (sext v_24 32))) v_38);
      let v_40 <- eval (concat (add (mul (sext v_17 32) (sext v_18 32)) (mul (sext v_19 32) (sext v_20 32))) v_39);
      let v_41 <- eval (concat (add (mul (sext v_13 32) (sext v_14 32)) (mul (sext v_15 32) (sext v_16 32))) v_40);
      let v_42 <- eval (concat (add (mul (sext v_9 32) (sext v_10 32)) (mul (sext v_11 32) (sext v_12 32))) v_41);
      let v_43 <- eval (concat (add (mul (sext v_4 32) (sext v_6 32)) (mul (sext v_7 32) (sext v_8 32))) v_42);
      setRegister (lhs.of_reg ymm_2) v_43;
      pure ()
     action
