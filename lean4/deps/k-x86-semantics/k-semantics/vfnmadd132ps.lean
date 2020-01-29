def vfnmadd132ps : instruction :=
  definst "vfnmadd132ps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 16;
      (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_8 32 64);
      (v_13 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_14 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_15 : expression (bv 32)) <- eval (extract v_8 64 96);
      (v_16 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_17 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_18 : expression (bv 32)) <- eval (extract v_8 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (/- (_,_,_) -/ vfnmadd132_single v_4 v_6 v_9) (concat (/- (_,_,_) -/ vfnmadd132_single v_10 v_11 v_12) (concat (/- (_,_,_) -/ vfnmadd132_single v_13 v_14 v_15) (/- (_,_,_) -/ vfnmadd132_single v_16 v_17 v_18))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_2);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 32;
      (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_8 32 64);
      (v_13 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_14 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_15 : expression (bv 32)) <- eval (extract v_8 64 96);
      (v_16 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_17 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_18 : expression (bv 32)) <- eval (extract v_8 96 128);
      (v_19 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_20 : expression (bv 32)) <- eval (extract v_5 128 160);
      (v_21 : expression (bv 32)) <- eval (extract v_8 128 160);
      (v_22 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_23 : expression (bv 32)) <- eval (extract v_5 160 192);
      (v_24 : expression (bv 32)) <- eval (extract v_8 160 192);
      (v_25 : expression (bv 32)) <- eval (extract v_3 192 224);
      (v_26 : expression (bv 32)) <- eval (extract v_5 192 224);
      (v_27 : expression (bv 32)) <- eval (extract v_8 192 224);
      (v_28 : expression (bv 32)) <- eval (extract v_3 224 256);
      (v_29 : expression (bv 32)) <- eval (extract v_5 224 256);
      (v_30 : expression (bv 32)) <- eval (extract v_8 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (/- (_,_,_) -/ vfnmadd132_single v_4 v_6 v_9) (concat (/- (_,_,_) -/ vfnmadd132_single v_10 v_11 v_12) (concat (/- (_,_,_) -/ vfnmadd132_single v_13 v_14 v_15) (concat (/- (_,_,_) -/ vfnmadd132_single v_16 v_17 v_18) (concat (/- (_,_,_) -/ vfnmadd132_single v_19 v_20 v_21) (concat (/- (_,_,_) -/ vfnmadd132_single v_22 v_23 v_24) (concat (/- (_,_,_) -/ vfnmadd132_single v_25 v_26 v_27) (/- (_,_,_) -/ vfnmadd132_single v_28 v_29 v_30))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      v_7 <- getRegister (lhs.of_reg xmm_0);
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_7 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_14 : expression (bv 32)) <- eval (extract v_7 64 96);
      (v_15 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_16 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_17 : expression (bv 32)) <- eval (extract v_7 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (/- (_,_,_) -/ vfnmadd132_single v_4 v_6 v_8) (concat (/- (_,_,_) -/ vfnmadd132_single v_9 v_10 v_11) (concat (/- (_,_,_) -/ vfnmadd132_single v_12 v_13 v_14) (/- (_,_,_) -/ vfnmadd132_single v_15 v_16 v_17))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_2);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      v_7 <- getRegister (lhs.of_reg ymm_0);
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_7 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_14 : expression (bv 32)) <- eval (extract v_7 64 96);
      (v_15 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_16 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_17 : expression (bv 32)) <- eval (extract v_7 96 128);
      (v_18 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_19 : expression (bv 32)) <- eval (extract v_5 128 160);
      (v_20 : expression (bv 32)) <- eval (extract v_7 128 160);
      (v_21 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_22 : expression (bv 32)) <- eval (extract v_5 160 192);
      (v_23 : expression (bv 32)) <- eval (extract v_7 160 192);
      (v_24 : expression (bv 32)) <- eval (extract v_3 192 224);
      (v_25 : expression (bv 32)) <- eval (extract v_5 192 224);
      (v_26 : expression (bv 32)) <- eval (extract v_7 192 224);
      (v_27 : expression (bv 32)) <- eval (extract v_3 224 256);
      (v_28 : expression (bv 32)) <- eval (extract v_5 224 256);
      (v_29 : expression (bv 32)) <- eval (extract v_7 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (/- (_,_,_) -/ vfnmadd132_single v_4 v_6 v_8) (concat (/- (_,_,_) -/ vfnmadd132_single v_9 v_10 v_11) (concat (/- (_,_,_) -/ vfnmadd132_single v_12 v_13 v_14) (concat (/- (_,_,_) -/ vfnmadd132_single v_15 v_16 v_17) (concat (/- (_,_,_) -/ vfnmadd132_single v_18 v_19 v_20) (concat (/- (_,_,_) -/ vfnmadd132_single v_21 v_22 v_23) (concat (/- (_,_,_) -/ vfnmadd132_single v_24 v_25 v_26) (/- (_,_,_) -/ vfnmadd132_single v_27 v_28 v_29))))))));
      pure ()
    pat_end
