def vpbroadcastd : instruction :=
  definst "vpbroadcastd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      setRegister (lhs.of_reg xmm_1) (concat (concat (concat v_3 v_3) v_3) v_3);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      setRegister (lhs.of_reg ymm_1) (concat (concat (concat (concat v_3 v_3) v_3) v_3) (concat (concat (concat v_3 v_3) v_3) v_3));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (concat (concat v_3 v_3) v_3) v_3);
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg ymm_1) (concat (concat (concat (concat v_3 v_3) v_3) v_3) (concat (concat (concat v_3 v_3) v_3) v_3));
      pure ()
    pat_end