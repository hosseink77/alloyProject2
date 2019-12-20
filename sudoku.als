
//Hossein karimi (39603129)

enum V {v1, v2, v3, v4, v5, v6, v7, v8, v9}

sig Cell {
  val: V,
  row: V,
  col: V
}


pred disjointSubgrid[rows: set V, cols: set V]{
  no disj c1, c2: Cell {
    c1.row in rows &&
    c2.row in rows &&
    c1.col in cols &&
    c2.col in cols &&
    c1.val = c2.val
    }
}

fact sudoku {
  #Cell = 81

  //One cell per grid location
  no disj x, y: Cell | x.col = y.col and x.row = y.row

  //distinct values per column and row
  no disj x, y: Cell | x.val = y.val and (x.col = y.col or x.row = y.row)

  //distinct values per subgrid
  let s1 = (v1 + v2 + v3) | let s2 = (v4 + v5 + v6) | let s3 = (v7 + v8 + v9) {
    disjointSubgrid[s1, s1]
    disjointSubgrid[s1, s2]
    disjointSubgrid[s1, s3]
    disjointSubgrid[s2, s1]
    disjointSubgrid[s2, s2]
    disjointSubgrid[s2, s3]
    disjointSubgrid[s3, s1]
    disjointSubgrid[s3, s2]
    disjointSubgrid[s3, s3]
  }
}

// * 2 3 * * 8 * 5 *
// * 8 * 9 * * 4 7 *
// * * * 5 * * * * *
// * 9 1 * 3 * * * *
// * * * 8 * * 5 * 6
// * * * * * 4 * * *
// * * * * 6 * * * *
// 7 * 9 * 8 * * * 5
// 6 * * * * 2 3 * 8
fact puzzle {
one c: Cell | c.row = v1 and c.col = v2 and c.val = v2
one c: Cell | c.row = v1 and c.col = v3 and c.val = v3
one c: Cell | c.row = v1 and c.col = v6 and c.val = v8
one c: Cell | c.row = v1 and c.col = v8 and c.val = v5
one c: Cell | c.row = v2 and c.col = v2 and c.val = v8
one c: Cell | c.row = v2 and c.col = v4 and c.val = v9
one c: Cell | c.row = v2 and c.col = v7 and c.val = v4
one c: Cell | c.row = v2 and c.col = v8 and c.val = v7
one c: Cell | c.row = v3 and c.col = v4 and c.val = v5
one c: Cell | c.row = v4 and c.col = v2 and c.val = v9
one c: Cell | c.row = v4 and c.col = v3 and c.val = v1
one c: Cell | c.row = v4 and c.col = v5 and c.val = v3
one c: Cell | c.row = v5 and c.col = v4 and c.val = v8
one c: Cell | c.row = v5 and c.col = v7 and c.val = v5
one c: Cell | c.row = v5 and c.col = v9 and c.val = v6
one c: Cell | c.row = v6 and c.col = v6 and c.val = v4
one c: Cell | c.row = v7 and c.col = v5 and c.val = v6
one c: Cell | c.row = v8 and c.col = v1 and c.val = v7
one c: Cell | c.row = v8 and c.col = v3 and c.val = v9
one c: Cell | c.row = v8 and c.col = v5 and c.val = v8
one c: Cell | c.row = v8 and c.col = v9 and c.val = v5
one c: Cell | c.row = v9 and c.col = v1 and c.val = v6
one c: Cell | c.row = v9 and c.col = v6 and c.val = v2
one c: Cell | c.row = v9 and c.col = v7 and c.val = v3
one c: Cell | c.row = v9 and c.col = v9 and c.val = v8
}


pred show {}

run show for 81 but 8 Int
