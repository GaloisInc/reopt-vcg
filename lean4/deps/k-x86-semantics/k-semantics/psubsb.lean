def psubsb : instruction :=
  definst "psubsb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      v_7 <- eval (sub (sext v_3 10) (sext v_6 10));
      (v_8 : expression (bv 8)) <- eval (extract v_7 2 10);
      (v_9 : expression (bv 8)) <- eval (extract v_2 8 16);
      (v_10 : expression (bv 8)) <- eval (extract v_5 8 16);
      v_11 <- eval (sub (sext v_9 10) (sext v_10 10));
      (v_12 : expression (bv 8)) <- eval (extract v_11 2 10);
      (v_13 : expression (bv 8)) <- eval (extract v_2 16 24);
      (v_14 : expression (bv 8)) <- eval (extract v_5 16 24);
      v_15 <- eval (sub (sext v_13 10) (sext v_14 10));
      (v_16 : expression (bv 8)) <- eval (extract v_15 2 10);
      (v_17 : expression (bv 8)) <- eval (extract v_2 24 32);
      (v_18 : expression (bv 8)) <- eval (extract v_5 24 32);
      v_19 <- eval (sub (sext v_17 10) (sext v_18 10));
      (v_20 : expression (bv 8)) <- eval (extract v_19 2 10);
      (v_21 : expression (bv 8)) <- eval (extract v_2 32 40);
      (v_22 : expression (bv 8)) <- eval (extract v_5 32 40);
      v_23 <- eval (sub (sext v_21 10) (sext v_22 10));
      (v_24 : expression (bv 8)) <- eval (extract v_23 2 10);
      (v_25 : expression (bv 8)) <- eval (extract v_2 40 48);
      (v_26 : expression (bv 8)) <- eval (extract v_5 40 48);
      v_27 <- eval (sub (sext v_25 10) (sext v_26 10));
      (v_28 : expression (bv 8)) <- eval (extract v_27 2 10);
      (v_29 : expression (bv 8)) <- eval (extract v_2 48 56);
      (v_30 : expression (bv 8)) <- eval (extract v_5 48 56);
      v_31 <- eval (sub (sext v_29 10) (sext v_30 10));
      (v_32 : expression (bv 8)) <- eval (extract v_31 2 10);
      (v_33 : expression (bv 8)) <- eval (extract v_2 56 64);
      (v_34 : expression (bv 8)) <- eval (extract v_5 56 64);
      v_35 <- eval (sub (sext v_33 10) (sext v_34 10));
      (v_36 : expression (bv 8)) <- eval (extract v_35 2 10);
      (v_37 : expression (bv 8)) <- eval (extract v_2 64 72);
      (v_38 : expression (bv 8)) <- eval (extract v_5 64 72);
      v_39 <- eval (sub (sext v_37 10) (sext v_38 10));
      (v_40 : expression (bv 8)) <- eval (extract v_39 2 10);
      (v_41 : expression (bv 8)) <- eval (extract v_2 72 80);
      (v_42 : expression (bv 8)) <- eval (extract v_5 72 80);
      v_43 <- eval (sub (sext v_41 10) (sext v_42 10));
      (v_44 : expression (bv 8)) <- eval (extract v_43 2 10);
      (v_45 : expression (bv 8)) <- eval (extract v_2 80 88);
      (v_46 : expression (bv 8)) <- eval (extract v_5 80 88);
      v_47 <- eval (sub (sext v_45 10) (sext v_46 10));
      (v_48 : expression (bv 8)) <- eval (extract v_47 2 10);
      (v_49 : expression (bv 8)) <- eval (extract v_2 88 96);
      (v_50 : expression (bv 8)) <- eval (extract v_5 88 96);
      v_51 <- eval (sub (sext v_49 10) (sext v_50 10));
      (v_52 : expression (bv 8)) <- eval (extract v_51 2 10);
      (v_53 : expression (bv 8)) <- eval (extract v_2 96 104);
      (v_54 : expression (bv 8)) <- eval (extract v_5 96 104);
      v_55 <- eval (sub (sext v_53 10) (sext v_54 10));
      (v_56 : expression (bv 8)) <- eval (extract v_55 2 10);
      (v_57 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_58 : expression (bv 8)) <- eval (extract v_5 104 112);
      v_59 <- eval (sub (sext v_57 10) (sext v_58 10));
      (v_60 : expression (bv 8)) <- eval (extract v_59 2 10);
      (v_61 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_62 : expression (bv 8)) <- eval (extract v_5 112 120);
      v_63 <- eval (sub (sext v_61 10) (sext v_62 10));
      (v_64 : expression (bv 8)) <- eval (extract v_63 2 10);
      (v_65 : expression (bv 8)) <- eval (extract v_2 120 128);
      (v_66 : expression (bv 8)) <- eval (extract v_5 120 128);
      v_67 <- eval (sub (sext v_65 10) (sext v_66 10));
      (v_68 : expression (bv 8)) <- eval (extract v_67 2 10);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_7 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_7 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_8)) (concat (mux (sgt v_11 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_12)) (concat (mux (sgt v_15 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_15 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_16)) (concat (mux (sgt v_19 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_19 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_20)) (concat (mux (sgt v_23 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_23 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_24)) (concat (mux (sgt v_27 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_27 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_28)) (concat (mux (sgt v_31 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_31 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_32)) (concat (mux (sgt v_35 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_35 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_36)) (concat (mux (sgt v_39 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_39 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_40)) (concat (mux (sgt v_43 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_43 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_44)) (concat (mux (sgt v_47 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_47 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_48)) (concat (mux (sgt v_51 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_51 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_52)) (concat (mux (sgt v_55 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_55 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_56)) (concat (mux (sgt v_59 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_59 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_60)) (concat (mux (sgt v_63 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_63 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_64)) (mux (sgt v_67 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_67 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_68)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 8)) <- eval (extract v_4 0 8);
      v_6 <- eval (sub (sext v_3 10) (sext v_5 10));
      (v_7 : expression (bv 8)) <- eval (extract v_6 2 10);
      (v_8 : expression (bv 8)) <- eval (extract v_2 8 16);
      (v_9 : expression (bv 8)) <- eval (extract v_4 8 16);
      v_10 <- eval (sub (sext v_8 10) (sext v_9 10));
      (v_11 : expression (bv 8)) <- eval (extract v_10 2 10);
      (v_12 : expression (bv 8)) <- eval (extract v_2 16 24);
      (v_13 : expression (bv 8)) <- eval (extract v_4 16 24);
      v_14 <- eval (sub (sext v_12 10) (sext v_13 10));
      (v_15 : expression (bv 8)) <- eval (extract v_14 2 10);
      (v_16 : expression (bv 8)) <- eval (extract v_2 24 32);
      (v_17 : expression (bv 8)) <- eval (extract v_4 24 32);
      v_18 <- eval (sub (sext v_16 10) (sext v_17 10));
      (v_19 : expression (bv 8)) <- eval (extract v_18 2 10);
      (v_20 : expression (bv 8)) <- eval (extract v_2 32 40);
      (v_21 : expression (bv 8)) <- eval (extract v_4 32 40);
      v_22 <- eval (sub (sext v_20 10) (sext v_21 10));
      (v_23 : expression (bv 8)) <- eval (extract v_22 2 10);
      (v_24 : expression (bv 8)) <- eval (extract v_2 40 48);
      (v_25 : expression (bv 8)) <- eval (extract v_4 40 48);
      v_26 <- eval (sub (sext v_24 10) (sext v_25 10));
      (v_27 : expression (bv 8)) <- eval (extract v_26 2 10);
      (v_28 : expression (bv 8)) <- eval (extract v_2 48 56);
      (v_29 : expression (bv 8)) <- eval (extract v_4 48 56);
      v_30 <- eval (sub (sext v_28 10) (sext v_29 10));
      (v_31 : expression (bv 8)) <- eval (extract v_30 2 10);
      (v_32 : expression (bv 8)) <- eval (extract v_2 56 64);
      (v_33 : expression (bv 8)) <- eval (extract v_4 56 64);
      v_34 <- eval (sub (sext v_32 10) (sext v_33 10));
      (v_35 : expression (bv 8)) <- eval (extract v_34 2 10);
      (v_36 : expression (bv 8)) <- eval (extract v_2 64 72);
      (v_37 : expression (bv 8)) <- eval (extract v_4 64 72);
      v_38 <- eval (sub (sext v_36 10) (sext v_37 10));
      (v_39 : expression (bv 8)) <- eval (extract v_38 2 10);
      (v_40 : expression (bv 8)) <- eval (extract v_2 72 80);
      (v_41 : expression (bv 8)) <- eval (extract v_4 72 80);
      v_42 <- eval (sub (sext v_40 10) (sext v_41 10));
      (v_43 : expression (bv 8)) <- eval (extract v_42 2 10);
      (v_44 : expression (bv 8)) <- eval (extract v_2 80 88);
      (v_45 : expression (bv 8)) <- eval (extract v_4 80 88);
      v_46 <- eval (sub (sext v_44 10) (sext v_45 10));
      (v_47 : expression (bv 8)) <- eval (extract v_46 2 10);
      (v_48 : expression (bv 8)) <- eval (extract v_2 88 96);
      (v_49 : expression (bv 8)) <- eval (extract v_4 88 96);
      v_50 <- eval (sub (sext v_48 10) (sext v_49 10));
      (v_51 : expression (bv 8)) <- eval (extract v_50 2 10);
      (v_52 : expression (bv 8)) <- eval (extract v_2 96 104);
      (v_53 : expression (bv 8)) <- eval (extract v_4 96 104);
      v_54 <- eval (sub (sext v_52 10) (sext v_53 10));
      (v_55 : expression (bv 8)) <- eval (extract v_54 2 10);
      (v_56 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_57 : expression (bv 8)) <- eval (extract v_4 104 112);
      v_58 <- eval (sub (sext v_56 10) (sext v_57 10));
      (v_59 : expression (bv 8)) <- eval (extract v_58 2 10);
      (v_60 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_61 : expression (bv 8)) <- eval (extract v_4 112 120);
      v_62 <- eval (sub (sext v_60 10) (sext v_61 10));
      (v_63 : expression (bv 8)) <- eval (extract v_62 2 10);
      (v_64 : expression (bv 8)) <- eval (extract v_2 120 128);
      (v_65 : expression (bv 8)) <- eval (extract v_4 120 128);
      v_66 <- eval (sub (sext v_64 10) (sext v_65 10));
      (v_67 : expression (bv 8)) <- eval (extract v_66 2 10);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_6 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_6 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_7)) (concat (mux (sgt v_10 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_11)) (concat (mux (sgt v_14 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_15)) (concat (mux (sgt v_18 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_18 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_19)) (concat (mux (sgt v_22 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_22 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_23)) (concat (mux (sgt v_26 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_26 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_27)) (concat (mux (sgt v_30 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_30 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_31)) (concat (mux (sgt v_34 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_34 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_35)) (concat (mux (sgt v_38 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_38 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_39)) (concat (mux (sgt v_42 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_42 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_43)) (concat (mux (sgt v_46 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_46 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_47)) (concat (mux (sgt v_50 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_50 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_51)) (concat (mux (sgt v_54 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_54 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_55)) (concat (mux (sgt v_58 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_58 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_59)) (concat (mux (sgt v_62 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_62 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_63)) (mux (sgt v_66 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_66 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) v_67)))))))))))))))));
      pure ()
    pat_end