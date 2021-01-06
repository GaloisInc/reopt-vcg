def vfmadd132sd : instruction :=
  definst "vfmadd132sd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      let v_8 <- evaluateAddress mem_0;
      let v_9 <- load v_8 8;
      let v_10 <- eval (concat v_4 (/- (_,_,_) -/ vfmadd132_double v_5 v_7 v_9));
      setRegister (lhs.of_reg xmm_2) v_10;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      let v_8 <- getRegister (lhs.of_reg xmm_0);
      let (v_9 : expression (bv 64)) <- eval (extract v_8 64 128);
      let v_10 <- eval (concat v_4 (/- (_,_,_) -/ vfmadd132_double v_5 v_7 v_9));
      setRegister (lhs.of_reg xmm_2) v_10;
      pure ()
     action
