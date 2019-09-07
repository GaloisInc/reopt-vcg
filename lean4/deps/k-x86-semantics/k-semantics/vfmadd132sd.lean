def vfmadd132sd1 : instruction :=
  definst "vfmadd132sd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister xmm_2;
      v_4 <- getRegister xmm_1;
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 8;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_3 64 128) (extract v_4 64 128) v_6));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister xmm_2;
      v_4 <- getRegister xmm_1;
      v_5 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_3 64 128) (extract v_4 64 128) (extract v_5 64 128)));
      pure ()
    pat_end
