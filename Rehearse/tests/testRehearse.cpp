#include <CelModel.h>
#include <CelNumVar.h>
#include <CelIntVar.h>
#include <CelBoolVar.h>
#include <CelNumVarArray.h>
#include <CelBoolVarArray.h>

#include "CbcModel.hpp"
#include "OsiClpSolverInterface.hpp"
#include "OsiCbcSolverInterface.hpp"

#include <list>
#include <iostream>
#include <CGAL/Exact_predicates_inexact_constructions_kernel.h>
#include <CGAL/convex_hull_2.h>
#include <CGAL/point_generators_2.h>
#include <CGAL/random_polygon_2.h>
#include <CGAL/Polygon_2.h>
#include <CGAL/Arr_segment_traits_2.h>
#include <CGAL/Arrangement_2.h>
#include <CGAL/aff_transformation_tags.h>
#include <math.h>
#include <CGAL/Arr_linear_traits_2.h>
#include <CGAL/Arrangement_2.h>
#include <CGAL/Arrangement_with_history_2.h>
#include <CGAL/Sweep_line_2_algorithms.h>
#include <CGAL/Arr_polyline_traits_2.h>
//#include <CGAL/Qt/TriangulationGraphicsItem.h>
#include <algorithm>
#include <CGAL/config.h>

typedef CGAL::Exact_predicates_inexact_constructions_kernel K;
typedef CGAL::Arr_linear_traits_2<K> Traits_2;
//typedef CGAL::Arr_segment_traits_2<K> Traits_2;
typedef CGAL::Arrangement_2<Traits_2> Arrangement_2;
typedef Traits_2::X_monotone_curve_2                  Segment_2;
typedef Traits_2::Point_2 Point_2;
typedef CGAL::Random_points_in_square_2<Point_2> Point_generator;
typedef std::list<Point_2>                         Container;
typedef CGAL::Polygon_2<Traits_2, Container>              Polygon_2;
typedef Polygon_2::Vertex_iterator VertexIterator;
typedef Arrangement_2::Vertex_handle                  Vertex_handle;
typedef Arrangement_2::Halfedge_handle                Halfedge_handle;
typedef Traits_2::Ray_2 Ray;
typedef CGAL::Direction_2<Traits_2> Direction;
typedef Traits_2::Aff_transformation_2                Aff_transformation_2;
typedef Traits_2::Curve_2 Curve_2;
//typedef CGAL::Arr_segment_traits_2<Traits_2>::Curve_2 Curve_2;
typedef CGAL::Arr_default_dcel< Traits_2 > Dcel;
typedef CGAL::Arrangement_with_history_2< Traits_2, Dcel > Arrangement;
//typedef Arrangement::Curve_2 Curve_2;
typedef Traits_2::X_monotone_curve_2                  X_monotone_curve_2;


using namespace rehearse;
static void setCover(std::vector<std::vector<int>> sets, int n) {
  OsiClpSolverInterface solver;
  CelModel model(solver);
  //CelVariableArray<CelIntVar> x;
  CelBoolVarArray x;
  x.multiDimensionResize(1,n);

  CelExpression objective;
  for(int i = 0; i < n; ++i) {
    objective += x[i];
  }
  model.setObjective(objective);

  //add set constraints
  for(auto set: sets) {
    CelExpression setConstraint;
    for(auto s: set) {
      setConstraint += x[s];
    }
    model.addConstraint(1 <= setConstraint);
  }
  for(int i = 0; i < n; ++i) {
    model.addConstraint(0 <= x[i]);
    model.addConstraint(x[i] <= 1);
  }
  solver.setObjSense(1.0);
  model.builderToSolver();
  solver.setLogLevel(0);
  solver.initialSolve();

  CbcModel cbcModel(solver);
  cbcModel.setLogLevel(1);
  cbcModel.solver()->setHintParam(OsiDoReducePrint, true, OsiHintTry);
  cbcModel.branchAndBound();
  for(int i = 0; i < n; ++i) {
    double xi = model.getSolutionValue(x[i], *cbcModel.solver());
    printf("Solution for x_%i : %g\n", i, xi);
  }
}


static bool containsEdge(Arrangement_2& arr, Arrangement_2::Halfedge_handle edge) {
  for(auto it = arr.edges_begin(); it != arr.edges_end(); ++it) {
    if(it->source() == edge->source() && it->source() == edge->source()
       ||it->source() == edge->target() && it->target() == edge->source())
      return true;
  }
  return false;
}

static Arrangement_2 insertRays(Arrangement_2 &arr, std::list<Ray> rays, bool secondary = false) {  
  for(auto r : rays) {
    Arrangement_2 orig(arr);
    Curve_2 c(r);
    // CGAL::insert(arr, c);    
    Traits_2 tr; 
    std::vector<CGAL::Object> zoneElems;
    CGAL::zone(arr,c, std::back_inserter(zoneElems));
    Arrangement_2::Halfedge_handle edge;
    for(auto e: zoneElems) {
      if(CGAL::assign(edge, e) && containsEdge(orig, edge) || secondary) {
	Arrangement_2::Halfedge ed = *edge;
	std::vector<Curve_2> cvec;
	cvec.push_back(ed.curve());
	cvec.push_back(c);
	std::list<Point_2> intersect;
	CGAL::compute_intersection_points(cvec.begin(), cvec.end(), std::back_inserter(intersect),false, tr);

	CGAL::insert(arr, Segment_2(intersect.front(), r.source()));

	}
    }
  }
  return arr;
}

static bool canUSee(Arrangement_2 *arr, Point_2 p1, Point_2 p2) {
  auto lineOfSight = Segment_2(p1,p2);
  std::vector<CGAL::Object> zoneElems;
  CGAL::zone(*arr, lineOfSight, std::back_inserter(zoneElems));
  auto uf = arr->unbounded_face();
  int hitOuterFace = 0;
  for(auto e: zoneElems){
    if(CGAL::assign(uf, e))
      ++hitOuterFace;
  }
  return (hitOuterFace > 0);
}

static std::map<Arrangement_2::Face *, int> createFaceIndex(Arrangement_2 &arr) {
  std::map<Arrangement_2::Face *, int> map;
  int i = 0;
  for(auto fit = arr.faces_begin(); fit != arr.faces_end(); ++fit, ++i){
    map.insert(std::make_pair(&(*fit),i));
  }
  return map;
}

static std::vector<std::vector<int>> & addReflex(std::list<Point_2> reflex,
						 std::vector<std::vector<int>> &sets,
						 Arrangement_2 &arr,
						 std::map<Arrangement_2::Face *, int> &index) {
  for(auto p : reflex) {
    std::vector<int> set;
    for(auto fit = arr.faces_begin(); fit != arr.faces_end(); ++fit)  {
      bool canSee = false;
      if(fit->has_outer_ccb())
	for(auto ccb1 = fit->outer_ccb(); ccb1 != fit->outer_ccb(); ++ccb1){
	  canSee = canSee || canUSee(&arr, ccb1->target()->point(),p);
	}
      if(canSee)
	set.push_back(index[&(*fit)]);
    }
    if(set.size()>0)
      sets.push_back(set);
  }
  return sets;
}

//add reflex vertices
static std::vector<std::vector<int>> createC2(Arrangement_2 &arr2,
					      Arrangement_2 &arr1,
					      std::list<Point_2> reflex) {
  std::vector<std::vector<int>> sets;
  auto map = createFaceIndex(arr2);
  for(auto f1 = arr1.faces_begin(); f1 != arr1.faces_end(); ++f1) {
    std::vector<int> set;
    for(auto f2 = arr1.faces_begin(); f2 != arr1.faces_end(); ++f2) {
      bool canSee = false;
      if(f1->has_outer_ccb())
      for(auto ccb1 = f1->outer_ccb(); ccb1 != f1->outer_ccb(); ++ccb1)
	for(auto ccb2 = f2->outer_ccb(); ccb2 != f2->outer_ccb(); ++ccb2){
	  canSee = canSee || canUSee(&arr2, ccb1->target()->point(),ccb2->target()->point());	    
	}
      if(canSee)
	set.push_back(map[&(*f2)]);
    }
    if(set.size() > 0)
      sets.push_back(set);
  }
  return sets; //addReflex(reflex,sets,arr2,map);
}
//add reflex vertices
static std::vector<std::vector<int>> createC1(Arrangement_2 &arr2,
					      Arrangement_2 &arr1,
					      std::list<Point_2> reflex) {
  auto n = arr2.number_of_faces();
  std::vector<std::vector<int>> sets;
  auto map = createFaceIndex(arr2);

  for(auto vit = arr1.vertices_begin(); vit != arr1.vertices_end(); ++vit) {
    std::vector<int> set;
    for(auto fit = arr2.faces_begin(); fit != arr2.faces_end(); ++fit) {
      bool canSee = false;
      if(fit->has_outer_ccb())
      for(auto ccb = fit->outer_ccb(); ccb != fit->outer_ccb(); ++ccb) {            
	canSee = canSee || canUSee(&arr2, vit->point(), ccb->target()->point()); 
      }
      if(canSee){
	set.push_back(map[&(*fit)]);
      }
    }
    if(set.size()> 0) {
      sets.push_back(set);
    }
  }
  return sets;//addReflex(reflex,sets,arr2,map);
}

static std::list<Ray> getRays(std::list<Point_2> reflex) {
  std::list<Ray> rays;
  //takes cos angle, sin angle
  Aff_transformation_2 rotate(CGAL::ROTATION,std::sin(M_PI/100.0),std::cos(M_PI/100.0)); 
  Aff_transformation_2 rational_rotate(CGAL::ROTATION,Direction(1,1), 1, 100); 
  for(auto p: reflex) {
    Ray r(p, Direction(p.x(),p.y()));
    for(int i = 0; i < 5; ++i) {
      std::cout << r.direction() << std::endl;
      rays.push_back(r);
      auto d = r.direction();
      r = Ray(p, rotate(r.direction()));
    }
  }
  return rays;
}

static Arrangement_2 arrFromPoly(Polygon_2 *poly) {
  Arrangement_2 arr;
  auto uf = arr.unbounded_face();
  auto ei = arr.insert_in_face_interior(*(poly->edges_begin()),uf);
  std::cout << *(poly->edges_begin()) << std::endl;
  auto vi = ei->source();
  for(auto e = ++(poly->edges_begin()); e !=poly->edges_end(); ++e) {
    auto ei = arr.insert_from_left_vertex(*e, vi);
    vi = ei->source();
  }
  return arr;
}
static bool isReflex(Point_2 p1, Point_2 p2, Point_2 p3, K* k) {
  std::cout <<"(" << p1 << ")(" << p2 << ")(" << p3 <<")" << std::endl;
  return k->orientation_2_object()(p1,p2,p3) == CGAL::RIGHT_TURN;
}

static std::list<Point_2> getReflex(Polygon_2 * polygon, K* k) {
  std::list<Point_2> reflexVertices;
  VertexIterator prev = polygon->vertices_begin();
  VertexIterator curr = ++polygon->vertices_begin();
  VertexIterator next = ++(++polygon->vertices_begin());
  //tests all but first and last
  
  for(;next != polygon->vertices_end(); ++prev,++curr,++next) {
    if(isReflex(*prev,*curr,*next,k))
      reflexVertices.push_back(*curr);
  }
  if(isReflex(*curr, *(++polygon->vertices_begin()),*(++(++polygon->vertices_begin())),k))
    reflexVertices.push_back(*(++polygon->vertices_begin()));
  if(isReflex(*prev,*curr,*(++polygon->vertices_begin()),k))
    reflexVertices.push_back(*curr);

  return reflexVertices;
}
//take a random polygon and find reflex vertices
int main() {
  K k;
  Polygon_2 polygon;
  Arrangement_2 arr, ar;
  std::cout << "My CGAL library is " << CGAL_VERSION_STR << " (1MMmmb1000)" << std::endl; 
  //std::cout << ar << std::endl;
  CGAL::random_polygon_2(4, std::back_inserter(polygon),
			 Point_generator(0.5));
  std::cout << "isConvext? " << polygon.is_convex() << std::endl <<
    getReflex(&polygon,&k).size() << std::endl;

  arr = arrFromPoly(&polygon);
  //std::cout << arr << std::endl;
  
  auto ref = getReflex(&polygon,&k);
  auto p1 = Point_2(-0.121362, 0.20947);
  std::list<Point_2> li;
  li.push_back(p1);
  auto rays = getRays(ref);
  arr = insertRays(arr,rays);
  std::cout << arr << std::endl;
  auto t = Traits_2();
  std::list<Point_2>     intersects;
  std::list<Curve_2> c;
  //instead make a new iterator???
  for(auto it = arr.edges_begin(); it != arr.edges_end(); ++it) {
    c.push_back(it->curve());
  }
  CGAL::compute_intersection_points (c.begin(), c.end(),
				      std::back_inserter (intersects));
  
  /*
   Test code, should contain exactly one reflex vertex
  auto p1 = Point_2(-0.121362, 0.20947);
  auto p2 = Point_2(0.0350855, 0.132129);
  auto p3 = Point_2(-0.231531, -0.313221);
  auto p4 = Point_2(0.17274, 0.173803);
  
  Polygon_2 pp;
  pp.push_back(p1);
  pp.push_back(p2);
  pp.push_back(p3);
  pp.push_back(p4);
  
  std::cout << isReflex(p1,p2,p3,&k) << std::endl;
  std::cout << getReflex(&pp,&k).size() << std::endl;
  */
  return 0;
}
