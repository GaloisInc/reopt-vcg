def paddq1 : instruction :=
  definst "paddq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      setRegister (lhs.of_reg xmm_1) (concat (add (extract v_2 0 64) (extract v_4 0 64)) (add (extract v_2 64 128) (extract v_4 64 128)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (add (extract v_2 0 64) (extract v_3 0 64)) (add (extract v_2 64 128) (extract v_3 64 128)));
      pure ()
    pat_end
