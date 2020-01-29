def pmovsxwd : instruction :=
  definst "pmovsxwd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_6 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      setRegister (lhs.of_reg xmm_1) (concat (sext v_4 32) (concat (sext v_5 32) (concat (sext v_6 32) (sext v_7 32))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_4 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_5 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_6 : expression (bv 16)) <- eval (extract v_2 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (sext v_3 32) (concat (sext v_4 32) (concat (sext v_5 32) (sext v_6 32))));
      pure ()
    pat_end
