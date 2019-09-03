def vpunpckhqdq1 : instruction :=
  definst "vpunpckhqdq" $ do
    pattern fun (v_2624 : reg (bv 128)) (v_2625 : reg (bv 128)) (v_2626 : reg (bv 128)) => do
      v_6303 <- getRegister v_2624;
      v_6305 <- getRegister v_2625;
      setRegister (lhs.of_reg v_2626) (concat (extract v_6303 0 64) (extract v_6305 0 64));
      pure ()
    pat_end;
    pattern fun (v_2634 : reg (bv 256)) (v_2635 : reg (bv 256)) (v_2636 : reg (bv 256)) => do
      v_6314 <- getRegister v_2634;
      v_6316 <- getRegister v_2635;
      setRegister (lhs.of_reg v_2636) (concat (concat (extract v_6314 0 64) (extract v_6316 0 64)) (concat (extract v_6314 128 192) (extract v_6316 128 192)));
      pure ()
    pat_end;
    pattern fun (v_2618 : Mem) (v_2619 : reg (bv 128)) (v_2620 : reg (bv 128)) => do
      v_12618 <- evaluateAddress v_2618;
      v_12619 <- load v_12618 16;
      v_12621 <- getRegister v_2619;
      setRegister (lhs.of_reg v_2620) (concat (extract v_12619 0 64) (extract v_12621 0 64));
      pure ()
    pat_end;
    pattern fun (v_2629 : Mem) (v_2630 : reg (bv 256)) (v_2631 : reg (bv 256)) => do
      v_12625 <- evaluateAddress v_2629;
      v_12626 <- load v_12625 32;
      v_12628 <- getRegister v_2630;
      setRegister (lhs.of_reg v_2631) (concat (concat (extract v_12626 0 64) (extract v_12628 0 64)) (concat (extract v_12626 128 192) (extract v_12628 128 192)));
      pure ()
    pat_end
