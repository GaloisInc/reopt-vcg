def vsqrtss : instruction :=
  definst "vsqrtss" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 4;
      let v_7 <- eval (concat v_4 (/- (_) -/ sqrt_single v_6));
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_7 <- eval (concat v_4 (/- (_) -/ sqrt_single v_6));
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action
