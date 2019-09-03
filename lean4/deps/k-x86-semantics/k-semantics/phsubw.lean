def phsubw1 : instruction :=
  definst "phsubw" $ do
    pattern fun (v_2496 : reg (bv 128)) (v_2497 : reg (bv 128)) => do
      v_4348 <- getRegister v_2496;
      v_4364 <- getRegister v_2497;
      setRegister (lhs.of_reg v_2497) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_4348 16 32) (extract v_4348 0 16)) (sub (extract v_4348 48 64) (extract v_4348 32 48))) (sub (extract v_4348 80 96) (extract v_4348 64 80))) (sub (extract v_4348 112 128) (extract v_4348 96 112))) (sub (extract v_4364 16 32) (extract v_4364 0 16))) (sub (extract v_4364 48 64) (extract v_4364 32 48))) (sub (extract v_4364 80 96) (extract v_4364 64 80))) (sub (extract v_4364 112 128) (extract v_4364 96 112)));
      pure ()
    pat_end;
    pattern fun (v_2492 : Mem) (v_2493 : reg (bv 128)) => do
      v_11464 <- evaluateAddress v_2492;
      v_11465 <- load v_11464 16;
      v_11481 <- getRegister v_2493;
      setRegister (lhs.of_reg v_2493) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_11465 16 32) (extract v_11465 0 16)) (sub (extract v_11465 48 64) (extract v_11465 32 48))) (sub (extract v_11465 80 96) (extract v_11465 64 80))) (sub (extract v_11465 112 128) (extract v_11465 96 112))) (sub (extract v_11481 16 32) (extract v_11481 0 16))) (sub (extract v_11481 48 64) (extract v_11481 32 48))) (sub (extract v_11481 80 96) (extract v_11481 64 80))) (sub (extract v_11481 112 128) (extract v_11481 96 112)));
      pure ()
    pat_end
