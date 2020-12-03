def vsqrtpd : instruction :=
  definst "vsqrtpd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_6 <- eval (concat (/- (_) -/ sqrt_double v_4) (/- (_) -/ sqrt_double v_5));
      setRegister (lhs.of_reg xmm_1) v_6;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 32;
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_6 : expression (bv 64)) <- eval (extract v_3 128 192);
      let (v_7 : expression (bv 64)) <- eval (extract v_3 192 256);
      let v_8 <- eval (concat (/- (_) -/ sqrt_double v_6) (/- (_) -/ sqrt_double v_7));
      let v_9 <- eval (concat (/- (_) -/ sqrt_double v_5) v_8);
      let v_10 <- eval (concat (/- (_) -/ sqrt_double v_4) v_9);
      setRegister (lhs.of_reg ymm_1) v_10;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      let (v_4 : expression (bv 64)) <- eval (extract v_2 64 128);
      let v_5 <- eval (concat (/- (_) -/ sqrt_double v_3) (/- (_) -/ sqrt_double v_4));
      setRegister (lhs.of_reg xmm_1) v_5;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg ymm_0);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      let (v_4 : expression (bv 64)) <- eval (extract v_2 64 128);
      let (v_5 : expression (bv 64)) <- eval (extract v_2 128 192);
      let (v_6 : expression (bv 64)) <- eval (extract v_2 192 256);
      let v_7 <- eval (concat (/- (_) -/ sqrt_double v_5) (/- (_) -/ sqrt_double v_6));
      let v_8 <- eval (concat (/- (_) -/ sqrt_double v_4) v_7);
      let v_9 <- eval (concat (/- (_) -/ sqrt_double v_3) v_8);
      setRegister (lhs.of_reg ymm_1) v_9;
      pure ()
     action
