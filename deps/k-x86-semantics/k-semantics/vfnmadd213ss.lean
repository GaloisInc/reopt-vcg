def vfnmadd213ss : instruction :=
  definst "vfnmadd213ss" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_8 <- evaluateAddress mem_0;
      let v_9 <- load v_8 4;
      let v_10 <- eval (concat v_4 (/- (_,_,_) -/ vfnmadd213_single v_5 v_7 v_9));
      setRegister (lhs.of_reg xmm_2) v_10;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_8 <- getRegister (lhs.of_reg xmm_0);
      let (v_9 : expression (bv 32)) <- eval (extract v_8 96 128);
      let v_10 <- eval (concat v_4 (/- (_,_,_) -/ vfnmadd213_single v_5 v_7 v_9));
      setRegister (lhs.of_reg xmm_2) v_10;
      pure ()
     action
