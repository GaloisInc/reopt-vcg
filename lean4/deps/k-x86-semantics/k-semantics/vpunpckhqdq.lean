def vpunpckhqdq1 : instruction :=
  definst "vpunpckhqdq" $ do
    pattern fun (v_2688 : reg (bv 128)) (v_2689 : reg (bv 128)) (v_2690 : reg (bv 128)) => do
      v_6217 <- getRegister v_2688;
      v_6219 <- getRegister v_2689;
      setRegister (lhs.of_reg v_2690) (concat (extract v_6217 0 64) (extract v_6219 0 64));
      pure ()
    pat_end;
    pattern fun (v_2699 : reg (bv 256)) (v_2700 : reg (bv 256)) (v_2701 : reg (bv 256)) => do
      v_6228 <- getRegister v_2699;
      v_6230 <- getRegister v_2700;
      setRegister (lhs.of_reg v_2701) (concat (concat (extract v_6228 0 64) (extract v_6230 0 64)) (concat (extract v_6228 128 192) (extract v_6230 128 192)));
      pure ()
    pat_end;
    pattern fun (v_2682 : Mem) (v_2683 : reg (bv 128)) (v_2684 : reg (bv 128)) => do
      v_12291 <- evaluateAddress v_2682;
      v_12292 <- load v_12291 16;
      v_12294 <- getRegister v_2683;
      setRegister (lhs.of_reg v_2684) (concat (extract v_12292 0 64) (extract v_12294 0 64));
      pure ()
    pat_end;
    pattern fun (v_2693 : Mem) (v_2694 : reg (bv 256)) (v_2695 : reg (bv 256)) => do
      v_12298 <- evaluateAddress v_2693;
      v_12299 <- load v_12298 32;
      v_12301 <- getRegister v_2694;
      setRegister (lhs.of_reg v_2695) (concat (concat (extract v_12299 0 64) (extract v_12301 0 64)) (concat (extract v_12299 128 192) (extract v_12301 128 192)));
      pure ()
    pat_end
