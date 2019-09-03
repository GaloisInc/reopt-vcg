def movmskps1 : instruction :=
  definst "movmskps" $ do
    pattern fun (v_2536 : reg (bv 128)) (v_2537 : reg (bv 32)) => do
      v_3955 <- getRegister v_2536;
      setRegister (lhs.of_reg v_2537) (concat (expression.bv_nat 28 0) (concat (extract v_3955 0 1) (concat (extract v_3955 32 33) (concat (extract v_3955 64 65) (extract v_3955 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2541 : reg (bv 128)) (v_2542 : reg (bv 64)) => do
      v_3965 <- getRegister v_2541;
      setRegister (lhs.of_reg v_2542) (concat (expression.bv_nat 60 0) (concat (extract v_3965 0 1) (concat (extract v_3965 32 33) (concat (extract v_3965 64 65) (extract v_3965 96 97)))));
      pure ()
    pat_end
