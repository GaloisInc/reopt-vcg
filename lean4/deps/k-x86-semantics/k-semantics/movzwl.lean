def movzwl1 : instruction :=
  definst "movzwl" $ do
    pattern fun (v_2692 : reg (bv 16)) (v_2693 : reg (bv 32)) => do
      v_4087 <- getRegister v_2692;
      setRegister (lhs.of_reg v_2693) (concat (expression.bv_nat 16 0) v_4087);
      pure ()
    pat_end;
    pattern fun (v_2687 : Mem) (v_2688 : reg (bv 32)) => do
      v_8907 <- evaluateAddress v_2687;
      v_8908 <- load v_8907 2;
      setRegister (lhs.of_reg v_2688) (concat (expression.bv_nat 16 0) v_8908);
      pure ()
    pat_end
