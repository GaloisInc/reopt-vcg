def phsubw1 : instruction :=
  definst "phsubw" $ do
    pattern fun (v_2482 : reg (bv 128)) (v_2483 : reg (bv 128)) => do
      v_4367 <- getRegister v_2482;
      v_4383 <- getRegister v_2483;
      setRegister (lhs.of_reg v_2483) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_4367 16 32) (extract v_4367 0 16)) (sub (extract v_4367 48 64) (extract v_4367 32 48))) (sub (extract v_4367 80 96) (extract v_4367 64 80))) (sub (extract v_4367 112 128) (extract v_4367 96 112))) (sub (extract v_4383 16 32) (extract v_4383 0 16))) (sub (extract v_4383 48 64) (extract v_4383 32 48))) (sub (extract v_4383 80 96) (extract v_4383 64 80))) (sub (extract v_4383 112 128) (extract v_4383 96 112)));
      pure ()
    pat_end;
    pattern fun (v_2477 : Mem) (v_2478 : reg (bv 128)) => do
      v_11813 <- evaluateAddress v_2477;
      v_11814 <- load v_11813 16;
      v_11830 <- getRegister v_2478;
      setRegister (lhs.of_reg v_2478) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_11814 16 32) (extract v_11814 0 16)) (sub (extract v_11814 48 64) (extract v_11814 32 48))) (sub (extract v_11814 80 96) (extract v_11814 64 80))) (sub (extract v_11814 112 128) (extract v_11814 96 112))) (sub (extract v_11830 16 32) (extract v_11830 0 16))) (sub (extract v_11830 48 64) (extract v_11830 32 48))) (sub (extract v_11830 80 96) (extract v_11830 64 80))) (sub (extract v_11830 112 128) (extract v_11830 96 112)));
      pure ()
    pat_end
