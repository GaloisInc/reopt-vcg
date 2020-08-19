def vpunpckhdq : instruction :=
  definst "vpunpckhdq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      setRegister (lhs.of_reg xmm_2) (concat (concat v_5 v_7) (concat v_8 v_9));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- getRegister (lhs.of_reg ymm_1);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_4 128 160);
      (v_11 : expression (bv 32)) <- eval (extract v_6 128 160);
      (v_12 : expression (bv 32)) <- eval (extract v_4 160 192);
      (v_13 : expression (bv 32)) <- eval (extract v_6 160 192);
      setRegister (lhs.of_reg ymm_2) (concat (concat v_5 v_7) (concat (concat v_8 v_9) (concat (concat v_10 v_11) (concat v_12 v_13))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      setRegister (lhs.of_reg xmm_2) (concat (concat v_4 v_6) (concat v_7 v_8));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_10 : expression (bv 32)) <- eval (extract v_5 128 160);
      (v_11 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_12 : expression (bv 32)) <- eval (extract v_5 160 192);
      setRegister (lhs.of_reg ymm_2) (concat (concat v_4 v_6) (concat (concat v_7 v_8) (concat (concat v_9 v_10) (concat v_11 v_12))));
      pure ()
    pat_end