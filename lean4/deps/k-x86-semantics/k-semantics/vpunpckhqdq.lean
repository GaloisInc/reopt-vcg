def vpunpckhqdq1 : instruction :=
  definst "vpunpckhqdq" $ do
    pattern fun (v_2634 : reg (bv 128)) (v_2635 : reg (bv 128)) (v_2636 : reg (bv 128)) => do
      v_6168 <- getRegister v_2634;
      v_6170 <- getRegister v_2635;
      setRegister (lhs.of_reg v_2636) (concat (extract v_6168 0 64) (extract v_6170 0 64));
      pure ()
    pat_end;
    pattern fun (v_2645 : reg (bv 256)) (v_2646 : reg (bv 256)) (v_2647 : reg (bv 256)) => do
      v_6179 <- getRegister v_2645;
      v_6181 <- getRegister v_2646;
      setRegister (lhs.of_reg v_2647) (concat (concat (extract v_6179 0 64) (extract v_6181 0 64)) (concat (extract v_6179 128 192) (extract v_6181 128 192)));
      pure ()
    pat_end;
    pattern fun (v_2629 : Mem) (v_2630 : reg (bv 128)) (v_2631 : reg (bv 128)) => do
      v_12615 <- evaluateAddress v_2629;
      v_12616 <- load v_12615 16;
      v_12618 <- getRegister v_2630;
      setRegister (lhs.of_reg v_2631) (concat (extract v_12616 0 64) (extract v_12618 0 64));
      pure ()
    pat_end;
    pattern fun (v_2640 : Mem) (v_2641 : reg (bv 256)) (v_2642 : reg (bv 256)) => do
      v_12622 <- evaluateAddress v_2640;
      v_12623 <- load v_12622 32;
      v_12625 <- getRegister v_2641;
      setRegister (lhs.of_reg v_2642) (concat (concat (extract v_12623 0 64) (extract v_12625 0 64)) (concat (extract v_12623 128 192) (extract v_12625 128 192)));
      pure ()
    pat_end
