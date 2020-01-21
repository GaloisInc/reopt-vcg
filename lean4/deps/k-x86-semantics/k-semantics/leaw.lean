def leaw : instruction :=
  definst "leaw" $ do
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- evaluateAddress mem_0;
      setRegister (lhs.of_reg r16_1) (extract v_2 48 64);
      pure ()
    pat_end
