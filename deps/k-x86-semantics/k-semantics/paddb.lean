def paddb : instruction :=
  definst "paddb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      (v_7 : expression (bv 8)) <- eval (extract v_2 8 16);
      (v_8 : expression (bv 8)) <- eval (extract v_5 8 16);
      (v_9 : expression (bv 8)) <- eval (extract v_2 16 24);
      (v_10 : expression (bv 8)) <- eval (extract v_5 16 24);
      (v_11 : expression (bv 8)) <- eval (extract v_2 24 32);
      (v_12 : expression (bv 8)) <- eval (extract v_5 24 32);
      (v_13 : expression (bv 8)) <- eval (extract v_2 32 40);
      (v_14 : expression (bv 8)) <- eval (extract v_5 32 40);
      (v_15 : expression (bv 8)) <- eval (extract v_2 40 48);
      (v_16 : expression (bv 8)) <- eval (extract v_5 40 48);
      (v_17 : expression (bv 8)) <- eval (extract v_2 48 56);
      (v_18 : expression (bv 8)) <- eval (extract v_5 48 56);
      (v_19 : expression (bv 8)) <- eval (extract v_2 56 64);
      (v_20 : expression (bv 8)) <- eval (extract v_5 56 64);
      (v_21 : expression (bv 8)) <- eval (extract v_2 64 72);
      (v_22 : expression (bv 8)) <- eval (extract v_5 64 72);
      (v_23 : expression (bv 8)) <- eval (extract v_2 72 80);
      (v_24 : expression (bv 8)) <- eval (extract v_5 72 80);
      (v_25 : expression (bv 8)) <- eval (extract v_2 80 88);
      (v_26 : expression (bv 8)) <- eval (extract v_5 80 88);
      (v_27 : expression (bv 8)) <- eval (extract v_2 88 96);
      (v_28 : expression (bv 8)) <- eval (extract v_5 88 96);
      (v_29 : expression (bv 8)) <- eval (extract v_2 96 104);
      (v_30 : expression (bv 8)) <- eval (extract v_5 96 104);
      (v_31 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_32 : expression (bv 8)) <- eval (extract v_5 104 112);
      (v_33 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_34 : expression (bv 8)) <- eval (extract v_5 112 120);
      (v_35 : expression (bv 8)) <- eval (extract v_2 120 128);
      (v_36 : expression (bv 8)) <- eval (extract v_5 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (add v_3 v_6) (concat (add v_7 v_8) (concat (add v_9 v_10) (concat (add v_11 v_12) (concat (add v_13 v_14) (concat (add v_15 v_16) (concat (add v_17 v_18) (concat (add v_19 v_20) (concat (add v_21 v_22) (concat (add v_23 v_24) (concat (add v_25 v_26) (concat (add v_27 v_28) (concat (add v_29 v_30) (concat (add v_31 v_32) (concat (add v_33 v_34) (add v_35 v_36))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 8)) <- eval (extract v_4 0 8);
      (v_6 : expression (bv 8)) <- eval (extract v_2 8 16);
      (v_7 : expression (bv 8)) <- eval (extract v_4 8 16);
      (v_8 : expression (bv 8)) <- eval (extract v_2 16 24);
      (v_9 : expression (bv 8)) <- eval (extract v_4 16 24);
      (v_10 : expression (bv 8)) <- eval (extract v_2 24 32);
      (v_11 : expression (bv 8)) <- eval (extract v_4 24 32);
      (v_12 : expression (bv 8)) <- eval (extract v_2 32 40);
      (v_13 : expression (bv 8)) <- eval (extract v_4 32 40);
      (v_14 : expression (bv 8)) <- eval (extract v_2 40 48);
      (v_15 : expression (bv 8)) <- eval (extract v_4 40 48);
      (v_16 : expression (bv 8)) <- eval (extract v_2 48 56);
      (v_17 : expression (bv 8)) <- eval (extract v_4 48 56);
      (v_18 : expression (bv 8)) <- eval (extract v_2 56 64);
      (v_19 : expression (bv 8)) <- eval (extract v_4 56 64);
      (v_20 : expression (bv 8)) <- eval (extract v_2 64 72);
      (v_21 : expression (bv 8)) <- eval (extract v_4 64 72);
      (v_22 : expression (bv 8)) <- eval (extract v_2 72 80);
      (v_23 : expression (bv 8)) <- eval (extract v_4 72 80);
      (v_24 : expression (bv 8)) <- eval (extract v_2 80 88);
      (v_25 : expression (bv 8)) <- eval (extract v_4 80 88);
      (v_26 : expression (bv 8)) <- eval (extract v_2 88 96);
      (v_27 : expression (bv 8)) <- eval (extract v_4 88 96);
      (v_28 : expression (bv 8)) <- eval (extract v_2 96 104);
      (v_29 : expression (bv 8)) <- eval (extract v_4 96 104);
      (v_30 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_31 : expression (bv 8)) <- eval (extract v_4 104 112);
      (v_32 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_33 : expression (bv 8)) <- eval (extract v_4 112 120);
      (v_34 : expression (bv 8)) <- eval (extract v_2 120 128);
      (v_35 : expression (bv 8)) <- eval (extract v_4 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (add v_3 v_5) (concat (add v_6 v_7) (concat (add v_8 v_9) (concat (add v_10 v_11) (concat (add v_12 v_13) (concat (add v_14 v_15) (concat (add v_16 v_17) (concat (add v_18 v_19) (concat (add v_20 v_21) (concat (add v_22 v_23) (concat (add v_24 v_25) (concat (add v_26 v_27) (concat (add v_28 v_29) (concat (add v_30 v_31) (concat (add v_32 v_33) (add v_34 v_35))))))))))))))));
      pure ()
    pat_end
