def vfnmadd132ss : instruction :=
  definst "vfnmadd132ss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      (v_5 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 32)) <- eval (extract v_6 96 128);
      v_8 <- evaluateAddress mem_0;
      v_9 <- load v_8 4;
      setRegister (lhs.of_reg xmm_2) (concat v_4 (/- (_,_,_) -/ vfnmadd132_single v_5 v_7 v_9));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      (v_5 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 32)) <- eval (extract v_6 96 128);
      v_8 <- getRegister (lhs.of_reg xmm_0);
      (v_9 : expression (bv 32)) <- eval (extract v_8 96 128);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (/- (_,_,_) -/ vfnmadd132_single v_5 v_7 v_9));
      pure ()
    pat_end
