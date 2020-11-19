def leaq : instruction :=
  definst "leaq" $ do
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- evaluateAddress mem_0;
      setRegister (lhs.of_reg r64_1) v_2;
      pure ()
    pat_end
