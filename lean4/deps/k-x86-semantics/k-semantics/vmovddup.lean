def vmovddup1 : instruction :=
  definst "vmovddup" $ do
    pattern fun (v_2828 : reg (bv 128)) (v_2829 : reg (bv 128)) => do
      v_4791 <- getRegister v_2828;
      setRegister (lhs.of_reg v_2829) (concat (extract v_4791 64 128) (extract v_4791 64 128));
      pure ()
    pat_end;
    pattern fun (v_2837 : reg (bv 256)) (v_2838 : reg (bv 256)) => do
      v_4799 <- getRegister v_2837;
      setRegister (lhs.of_reg v_2838) (concat (concat (extract v_4799 64 128) (extract v_4799 64 128)) (concat (extract v_4799 192 256) (extract v_4799 192 256)));
      pure ()
    pat_end;
    pattern fun (v_2824 : Mem) (v_2825 : reg (bv 128)) => do
      v_10174 <- evaluateAddress v_2824;
      v_10175 <- load v_10174 8;
      setRegister (lhs.of_reg v_2825) (concat v_10175 v_10175);
      pure ()
    pat_end;
    pattern fun (v_2833 : Mem) (v_2834 : reg (bv 256)) => do
      v_10178 <- evaluateAddress v_2833;
      v_10179 <- load v_10178 32;
      setRegister (lhs.of_reg v_2834) (concat (concat (extract v_10179 64 128) (extract v_10179 64 128)) (concat (extract v_10179 192 256) (extract v_10179 192 256)));
      pure ()
    pat_end
