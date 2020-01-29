def vpmovsxbq : instruction :=
  definst "vpmovsxbq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      setRegister (lhs.of_reg xmm_1) (concat (sext v_4 64) (sext v_5 64));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      setRegister (lhs.of_reg ymm_1) (concat (sext v_4 64) (concat (sext v_5 64) (concat (sext v_6 64) (sext v_7 64))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_4 : expression (bv 8)) <- eval (extract v_2 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (sext v_3 64) (sext v_4 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 8)) <- eval (extract v_2 96 104);
      (v_4 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_5 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_6 : expression (bv 8)) <- eval (extract v_2 120 128);
      setRegister (lhs.of_reg ymm_1) (concat (sext v_3 64) (concat (sext v_4 64) (concat (sext v_5 64) (sext v_6 64))));
      pure ()
    pat_end
