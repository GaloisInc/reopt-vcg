def vpandn1 : instruction :=
  definst "vpandn" $ do
    pattern fun (v_2608 : reg (bv 128)) (v_2609 : reg (bv 128)) (v_2610 : reg (bv 128)) => do
      v_5727 <- getRegister v_2609;
      v_5729 <- getRegister v_2608;
      setRegister (lhs.of_reg v_2610) (bv_and (bv_xor v_5727 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5729);
      pure ()
    pat_end;
    pattern fun (v_2618 : reg (bv 256)) (v_2619 : reg (bv 256)) (v_2620 : reg (bv 256)) => do
      v_5737 <- getRegister v_2619;
      v_5739 <- getRegister v_2618;
      setRegister (lhs.of_reg v_2620) (bv_and (bv_xor v_5737 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_5739);
      pure ()
    pat_end;
    pattern fun (v_2602 : Mem) (v_2603 : reg (bv 128)) (v_2604 : reg (bv 128)) => do
      v_14429 <- getRegister v_2603;
      v_14431 <- evaluateAddress v_2602;
      v_14432 <- load v_14431 16;
      setRegister (lhs.of_reg v_2604) (bv_and (bv_xor v_14429 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_14432);
      pure ()
    pat_end;
    pattern fun (v_2613 : Mem) (v_2614 : reg (bv 256)) (v_2615 : reg (bv 256)) => do
      v_14435 <- getRegister v_2614;
      v_14437 <- evaluateAddress v_2613;
      v_14438 <- load v_14437 32;
      setRegister (lhs.of_reg v_2615) (bv_and (bv_xor v_14435 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_14438);
      pure ()
    pat_end
