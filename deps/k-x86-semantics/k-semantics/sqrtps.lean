def sqrtps : instruction :=
  definst "sqrtps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_8 <- eval (concat (/- (_) -/ sqrt_single v_6) (/- (_) -/ sqrt_single v_7));
      let v_9 <- eval (concat (/- (_) -/ sqrt_single v_5) v_8);
      let v_10 <- eval (concat (/- (_) -/ sqrt_single v_4) v_9);
      setRegister (lhs.of_reg xmm_1) v_10;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let (v_4 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_5 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_7 <- eval (concat (/- (_) -/ sqrt_single v_5) (/- (_) -/ sqrt_single v_6));
      let v_8 <- eval (concat (/- (_) -/ sqrt_single v_4) v_7);
      let v_9 <- eval (concat (/- (_) -/ sqrt_single v_3) v_8);
      setRegister (lhs.of_reg xmm_1) v_9;
      pure ()
     action
