def vmovsldup : instruction :=
  definst "vmovsldup" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_5 : expression (bv 32)) <- eval (extract v_3 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (concat v_4 v_4) (concat v_5 v_5));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_5 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_6 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_7 : expression (bv 32)) <- eval (extract v_3 224 256);
      setRegister (lhs.of_reg ymm_1) (concat (concat (concat v_4 v_4) (concat v_5 v_5)) (concat (concat v_6 v_6) (concat v_7 v_7)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_4 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (concat v_3 v_3) (concat v_4 v_4));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_4 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_5 : expression (bv 32)) <- eval (extract v_2 160 192);
      (v_6 : expression (bv 32)) <- eval (extract v_2 224 256);
      setRegister (lhs.of_reg ymm_1) (concat (concat (concat v_3 v_3) (concat v_4 v_4)) (concat (concat v_5 v_5) (concat v_6 v_6)));
      pure ()
    pat_end