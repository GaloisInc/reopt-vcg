def punpckhbw1 : instruction :=
  definst "punpckhbw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_1) (concat (concat (extract v_3 0 8) (extract v_4 0 8)) (concat (concat (extract v_3 8 16) (extract v_4 8 16)) (concat (concat (extract v_3 16 24) (extract v_4 16 24)) (concat (concat (extract v_3 24 32) (extract v_4 24 32)) (concat (concat (extract v_3 32 40) (extract v_4 32 40)) (concat (concat (extract v_3 40 48) (extract v_4 40 48)) (concat (concat (extract v_3 48 56) (extract v_4 48 56)) (concat (extract v_3 56 64) (extract v_4 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_1) (concat (concat (extract v_2 0 8) (extract v_3 0 8)) (concat (concat (extract v_2 8 16) (extract v_3 8 16)) (concat (concat (extract v_2 16 24) (extract v_3 16 24)) (concat (concat (extract v_2 24 32) (extract v_3 24 32)) (concat (concat (extract v_2 32 40) (extract v_3 32 40)) (concat (concat (extract v_2 40 48) (extract v_3 40 48)) (concat (concat (extract v_2 48 56) (extract v_3 48 56)) (concat (extract v_2 56 64) (extract v_3 56 64)))))))));
      pure ()
    pat_end
