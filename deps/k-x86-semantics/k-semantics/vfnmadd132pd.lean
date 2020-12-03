def vfnmadd132pd : instruction :=
  definst "vfnmadd132pd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- evaluateAddress mem_0;
      let v_8 <- load v_7 16;
      let (v_9 : expression (bv 64)) <- eval (extract v_8 0 64);
      let (v_10 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_11 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_12 : expression (bv 64)) <- eval (extract v_8 64 128);
      let v_13 <- eval (concat (/- (_,_,_) -/ vfnmadd132_double v_4 v_6 v_9) (/- (_,_,_) -/ vfnmadd132_double v_10 v_11 v_12));
      setRegister (lhs.of_reg xmm_2) v_13;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- evaluateAddress mem_0;
      let v_8 <- load v_7 32;
      let (v_9 : expression (bv 64)) <- eval (extract v_8 0 64);
      let (v_10 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_11 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_12 : expression (bv 64)) <- eval (extract v_8 64 128);
      let (v_13 : expression (bv 64)) <- eval (extract v_3 128 192);
      let (v_14 : expression (bv 64)) <- eval (extract v_5 128 192);
      let (v_15 : expression (bv 64)) <- eval (extract v_8 128 192);
      let (v_16 : expression (bv 64)) <- eval (extract v_3 192 256);
      let (v_17 : expression (bv 64)) <- eval (extract v_5 192 256);
      let (v_18 : expression (bv 64)) <- eval (extract v_8 192 256);
      let v_19 <- eval (concat (/- (_,_,_) -/ vfnmadd132_double v_13 v_14 v_15) (/- (_,_,_) -/ vfnmadd132_double v_16 v_17 v_18));
      let v_20 <- eval (concat (/- (_,_,_) -/ vfnmadd132_double v_10 v_11 v_12) v_19);
      let v_21 <- eval (concat (/- (_,_,_) -/ vfnmadd132_double v_4 v_6 v_9) v_20);
      setRegister (lhs.of_reg ymm_2) v_21;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- getRegister (lhs.of_reg xmm_0);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      let (v_9 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_10 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_11 : expression (bv 64)) <- eval (extract v_7 64 128);
      let v_12 <- eval (concat (/- (_,_,_) -/ vfnmadd132_double v_4 v_6 v_8) (/- (_,_,_) -/ vfnmadd132_double v_9 v_10 v_11));
      setRegister (lhs.of_reg xmm_2) v_12;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- getRegister (lhs.of_reg ymm_0);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      let (v_9 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_10 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_11 : expression (bv 64)) <- eval (extract v_7 64 128);
      let (v_12 : expression (bv 64)) <- eval (extract v_3 128 192);
      let (v_13 : expression (bv 64)) <- eval (extract v_5 128 192);
      let (v_14 : expression (bv 64)) <- eval (extract v_7 128 192);
      let (v_15 : expression (bv 64)) <- eval (extract v_3 192 256);
      let (v_16 : expression (bv 64)) <- eval (extract v_5 192 256);
      let (v_17 : expression (bv 64)) <- eval (extract v_7 192 256);
      let v_18 <- eval (concat (/- (_,_,_) -/ vfnmadd132_double v_12 v_13 v_14) (/- (_,_,_) -/ vfnmadd132_double v_15 v_16 v_17));
      let v_19 <- eval (concat (/- (_,_,_) -/ vfnmadd132_double v_9 v_10 v_11) v_18);
      let v_20 <- eval (concat (/- (_,_,_) -/ vfnmadd132_double v_4 v_6 v_8) v_19);
      setRegister (lhs.of_reg ymm_2) v_20;
      pure ()
     action
