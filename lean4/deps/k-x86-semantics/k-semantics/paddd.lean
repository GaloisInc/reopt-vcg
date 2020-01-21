def paddd : instruction :=
  definst "paddd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      setRegister (lhs.of_reg xmm_1) (concat (add (extract v_2 0 32) (extract v_4 0 32)) (concat (add (extract v_2 32 64) (extract v_4 32 64)) (concat (add (extract v_2 64 96) (extract v_4 64 96)) (add (extract v_2 96 128) (extract v_4 96 128)))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (add (extract v_2 0 32) (extract v_3 0 32)) (concat (add (extract v_2 32 64) (extract v_3 32 64)) (concat (add (extract v_2 64 96) (extract v_3 64 96)) (add (extract v_2 96 128) (extract v_3 96 128)))));
      pure ()
    pat_end
